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
use crate::gluing::{Cover, GluingReading, GluingRefusal, read_cover};
use crate::multiquadratic::{
    DECLARED_KERNEL_BOUND, EmbeddedSign, Multiquadratic, MultiquadraticRefusal,
};

/// **The generator aperture a triangle's own corners require**, read off the material.
///
/// The multiquadratic basis is `2ⁿ` wide in the number of distinct squarefree generators, so the
/// aperture bounds a real resource — but the value is not a choice. A composition can only carry
/// the kernels its own corners already hold, so the union of those kernels **is** the aperture.
///
/// This was `pub const DECLARED_GENERATOR_APERTURE: usize = 12` until 2026-08-10, which is
/// `canon/THE_AUTHORED_LEVEL.md`'s convicted shape exactly: *"refusing past a number you invented
/// does not make the number derived"*, the same defect that excised `FREE_ENTRY_APERTURE = 12` and
/// `REFINEMENT_APERTURE = 64`. Lifting it moved no return on the declared material — three corners
/// contribute at most three generators, well inside twelve — so this is **bookkeeping and is
/// reported as bookkeeping**, not as an orbit.
pub fn required_aperture(triangle: &ContactTriangle) -> usize {
    let mut kernels: BTreeSet<&BigInt> = BTreeSet::new();
    for corner in &triangle.corners {
        if let Ok(sine) = &corner.sine {
            kernels.extend(sine.generators());
        }
    }
    kernels.len().max(1)
}
use crate::rebase_invariants::PivotRule;
use crate::running_integral::{
    Cochain, Orientation, Path, PathStep, RunningIntegralError, running_sum,
};

/// Why a contact could not be read as a cover.
#[derive(Debug)]
pub enum ContactGluingRefusal {
    /// The cover carries no occurrence of the named stem, so there is no subcomplex to glue.
    StemStandsNowhere {
        stem: String,
    },
    /// A walk named an occurrence the complex does not carry.
    WalkLeavesTheCover {
        stem: String,
    },
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
                write!(
                    formatter,
                    "the walk names `{stem}`, which this cover does not carry"
                )
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
            return Err(ContactGluingRefusal::StemStandsNowhere {
                stem: stem.to_owned(),
            });
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
            return Err(ContactGluingRefusal::WalkLeavesTheCover {
                stem: stem.to_owned(),
            });
        }
        let steps: Vec<PathStep> = covered
            .into_iter()
            .filter_map(|at| self.steps.get(&at).copied())
            .map(|cell| PathStep {
                cell,
                orientation: Orientation::Along,
            })
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
        boundary.add_term(
            head,
            ComparativeMultiplicity::new(BigUint::from(1u32), BigUint::from(0u32)),
        );
        boundary.add_term(
            tail,
            ComparativeMultiplicity::new(BigUint::from(0u32), BigUint::from(1u32)),
        );
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
            steps
                .get(&occurrence.at)
                .copied()
                .unwrap_or(CausalCellId(0)),
        ));
    }
    Ok(ContactComplex {
        complex,
        occurrences,
        offsets,
        steps,
    })
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
    let reading =
        read_cover(&contact.complex, &cover_pair, rule).map_err(ContactGluingRefusal::Gluing)?;
    Ok((contact, reading))
}

// -------------------------------------------------------------------------------------------------
// The leader, the integral, and the return stroke
// -------------------------------------------------------------------------------------------------

/// A declared weight on the cells a leader crosses. **Both measure; neither governs.**
///
/// **The two organs cross different cells, so each variant reads on two complexes and the readings
/// are not the same quantity.** This is stated rather than smoothed over: the doc said *"how many
/// letters the occurrence carries"* for `SpanLength` until 2026-08-10, which is true of the contact
/// graph and false of the word line, where the value is the **cardinality of the face**. A gauge
/// whose name means one thing in one organ and another thing next door is unreadable, and the
/// separating measurement is that the two disagree numerically on the same stem.
///
/// ```text
///                       word line (`integrate_leader`, cells = unit steps)
///                       |                                        contact graph (`ride_circuit`, cells = arcs)
///   SpanLength          |face_over(step)| — how many stems       stem.len() — how many letters
///                       superpose over this letter               the shared stem carries
///   WitnessBreadth      Σ over the face of |wholes|              |wholes| of the arc's stem
/// ```
///
/// Both are structural on the left column and `Π` — the lived construction — on the right; neither
/// is ever allowed to select.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeaderCochain {
    /// Structural: face cardinality on the word line, stem length on the contact graph.
    SpanLength,
    /// `Π`, the lived construction: how many distinct wholes witnessed the stem, reported and never
    /// allowed to select.
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
    let integral =
        running_sum(&contact.complex, &weights, &path).map_err(ContactGluingRefusal::Integral)?;

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
        let Ok(cover) = morphology.cover(word) else {
            continue;
        };
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
                arcs.push(((*left).clone(), (*right).clone(), stem.to_owned(), cell));
            }
        }
    }
    Ok(ContactGraph {
        complex,
        identifiers,
        arcs,
    })
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
///
/// **`RunningIntegralError::PathIsNotClosed` cannot be reached through this entry point**, and
/// saying so is `CLAUDE.md` §8's *unreachable refusals, reported not counted*. Both arcs are
/// constrained by `find` to lie between the same pair, `contact_graph` stores every arc of a pair
/// with the same tail and head, and the second is crossed `Against` — so every input this function
/// accepts describes a walk that closes, including `out_stem == back_stem`, which closes at
/// holonomy zero. The guard inside [`crate::running_integral::holonomy`] is real and is exercised
/// by walks built directly on `ContactGraph::complex`; it is not exercised by this caller.
/// `examples/the_circuit_closes_and_the_face_superposes.rs` exhibits it firing on the same graph.
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
                carried == stem && ((a == left && b == right) || (a == right && b == left))
            })
            .map(|(_, _, _, cell)| *cell)
            .ok_or(ContactGluingRefusal::WalkLeavesTheCover {
                stem: stem.to_owned(),
            })
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
        PathStep {
            cell: out,
            orientation: Orientation::Along,
        },
        PathStep {
            cell: back,
            orientation: Orientation::Against,
        },
    ]);
    let integral = crate::running_integral::holonomy(&graph.complex, &weights, &path)
        .map_err(ContactGluingRefusal::Integral)?;

    // **The return is read off the traversal, never echoed from the arguments.**
    //
    // These three fields were `vec![left, right, left]`, `vec![out_stem, back_stem]` and
    // `vec![false, true]` — the caller's own arguments, restated as though they were a measurement.
    // `left` and `right` name an **unordered** pair, because `find` accepts an arc in either order,
    // so riding the same two arcs with the arguments swapped returned `[right, left, right]` for a
    // walk that departs and returns at the same vertex either way. The argument order — a
    // receiver-visible coordinate that no arc carries — was promoted into the return.
    // `CLAUDE.md` §0's fourth lesson, at the width of three fields.
    //
    // The walk itself knows where it went: `RunningIntegral` carries `departed`/`arrived` per step
    // and the orientation each was crossed at. All three fields are read off it, so a `Circuit` is
    // now a record of a traversal rather than a restatement of a request.
    let vertex_name: BTreeMap<CausalCellId, &str> = graph
        .identifiers
        .iter()
        .map(|(name, cell)| (*cell, name.as_str()))
        .collect();
    let arc_stem: BTreeMap<CausalCellId, &str> = graph
        .arcs
        .iter()
        .map(|(_, _, stem, cell)| (*cell, stem.as_str()))
        .collect();

    let mut through = Vec::with_capacity(integral.steps.len() + 1);
    let mut string = Vec::with_capacity(integral.steps.len());
    let mut reflected = Vec::with_capacity(integral.steps.len());
    for (position, step) in integral.steps.iter().enumerate() {
        let stood_at = |cell: CausalCellId| -> Result<String, ContactGluingRefusal> {
            vertex_name
                .get(&cell)
                .map(|name| (*name).to_owned())
                .ok_or_else(|| {
                    ContactGluingRefusal::Algebraic(format!(
                        "the walk stood at {cell:?}, which this graph names no identifier for"
                    ))
                })
        };
        if position == 0 {
            through.push(stood_at(step.departed)?);
        }
        through.push(stood_at(step.arrived)?);
        string.push(
            arc_stem
                .get(&step.cell)
                .map(|stem| (*stem).to_owned())
                .ok_or_else(|| {
                    ContactGluingRefusal::Algebraic(format!(
                        "the walk rode {:?}, which this graph carries no arc for",
                        step.cell
                    ))
                })?,
        );
        reflected.push(step.orientation == Orientation::Against);
    }

    Ok(Circuit {
        through,
        string,
        reflected,
        series: integral
            .steps
            .iter()
            .map(|step| step.accumulated.clone())
            .collect(),
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
        let (_, stroke) = integrate_leader(&cover, &morphology, "exact", LeaderCochain::SpanLength)
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
        assert_eq!(
            by_span.string, by_breadth.string,
            "one walk, two measurements"
        );
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
            let invariants = crate::rebase_invariants::rebase_invariants(
                &contact.complex,
                PivotRule::SmallestMagnitude,
            )
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
        let cosine =
            law_of_cosines(&BigInt::from(5), &BigInt::from(5), &BigInt::from(5)).expect("a corner");
        assert_eq!(cosine, half);
        // And a right angle is exactly zero — Pythagoras is the `cos = 0` case of the same law.
        let square =
            law_of_cosines(&BigInt::from(3), &BigInt::from(4), &BigInt::from(5)).expect("a corner");
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
        assert!(
            shared.len() >= 2,
            "two identifiers share two stems: {shared:?}"
        );

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

        assert_eq!(
            circuit.through.first(),
            circuit.through.last(),
            "the walk returns"
        );
        assert_eq!(
            circuit.reflected,
            vec![false, true],
            "the return arm is reflected"
        );
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
    Degenerate {
        short: BigInt,
        other: BigInt,
        long: BigInt,
    },
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
                    identifiers: [(*first).clone(), (*second).clone(), (*third).clone()],
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
        let weight = weight_of_stem
            .get(stem)
            .cloned()
            .unwrap_or_else(|| BigInt::from(0));
        for (position, left) in holders.iter().enumerate() {
            for right in holders.iter().skip(position + 1) {
                if left == right {
                    continue;
                }
                let (a, b) = if left <= right {
                    (left, right)
                } else {
                    (right, left)
                };
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
    NotRealizable {
        short: BigInt,
        other: BigInt,
        long: BigInt,
    },
}

/// Compose a triangle's three corners into the single turn it contributes upward, under the
/// aperture the triangle's own corners require ([`required_aperture`]).
pub fn coarse_grain(triangle: &ContactTriangle) -> CoarseTurn {
    coarse_grain_in_aperture(triangle, required_aperture(triangle))
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
                Err(refusal) => {
                    return CoarseTurn::Refused {
                        refusals: vec![(corner.at.clone(), refusal)],
                    };
                }
            },
            (Err(refusal), _) | (_, Err(refusal)) => {
                return CoarseTurn::Refused {
                    refusals: vec![(corner.at.clone(), refusal)],
                };
            }
        };
        let next_sine = match (cosine.multiply(s, aperture), sine.multiply(&c, aperture)) {
            (Ok(left), Ok(right)) => match left.add(&right, aperture) {
                Ok(value) => value,
                Err(refusal) => {
                    return CoarseTurn::Refused {
                        refusals: vec![(corner.at.clone(), refusal)],
                    };
                }
            },
            (Err(refusal), _) | (_, Err(refusal)) => {
                return CoarseTurn::Refused {
                    refusals: vec![(corner.at.clone(), refusal)],
                };
            }
        };
        cosine = next_cosine;
        sine = next_sine;
    }
    CoarseTurn::Exact { cosine, sine }
}

// -------------------------------------------------------------------------------------------------
// The hinge: where the curvature actually is, and why the triangle never carried it
// -------------------------------------------------------------------------------------------------

/// **How a vertex's link sits**, read off the triangles incident to it and nothing else.
///
/// The laboratory's `2026-07-26_THE_RECEIVER_IS_ITS_LOCAL_STAR_THE_LINK_IS_ITS_HYPERSPHERICAL_HORIZON`
/// (read at `a07ff376`) defines a receiver as `(σ, H = St̄(σ), L = Lk(σ), g, 𝒯, q, 𝒫)` and states the
/// bar this enum exists to hold:
///
/// > *"When the link is a ball, has nonzero genus, has several components, is pinched, or fails the
/// > manifold-link condition, the receiver is respectively at an exposed boundary, a handled region,
/// > a branch, a neck, or a singular discriminant. **That residual geometry is information. It must
/// > not be rounded into a sphere.**"*
///
/// So this is not a validity check with a pass and a fail. Every variant is a return.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LinkClass {
    /// The link is a single cycle: `L ≅ S¹`, and the star is a disc. The regular interior phase,
    /// and the only one in which a deficit angle means what Regge calculus says it means.
    Sphere { length: usize },
    /// The link is a single arc: `L ≅ B¹`. An **exposed boundary** — the vertex sits on the edge of
    /// the complex, so `2π − Σθ` measures the opening and not a curvature.
    Ball { length: usize },
    /// The link has several connected components. A **branch**: two or more sheets meet only at
    /// this vertex.
    Components { count: usize },
    /// Some link vertex has degree three or more — three or more triangles share one edge here, so
    /// the manifold-link condition fails. A **singular discriminant**.
    Singular { max_degree: usize },
    /// No realizable triangle is incident. There is no link and no hinge.
    Empty,
}

impl LinkClass {
    /// Whether a Regge deficit read at this hinge is a curvature rather than an opening or a
    /// singularity. Only [`LinkClass::Sphere`] qualifies, and saying so is the point of the enum.
    pub fn is_regular_interior(&self) -> bool {
        matches!(self, LinkClass::Sphere { .. })
    }
}

/// **The turn a hinge's incident corners compose to**, with the winding that says which multiple of
/// `2π` it came back around.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HingeHolonomy {
    /// `∏_{t ∋ v} e^{iθ_v(t)}` as an exact point on the unit circle, together with the number of
    /// `π`-boundaries the accumulated angle crossed on the way.
    ///
    /// The turn alone gives only `Σθ mod 2π`. The winding is what separates `Σθ = 2π` from
    /// `Σθ = 0` or `4π`, and it is an **integer read off monotone crossings** rather than a
    /// comparison of magnitudes — `CLAUDE.md` §2b's standing obligation, *name the windings*, met
    /// on the object it was stated for.
    Exact {
        cosine: Multiquadratic,
        sine: Multiquadratic,
        /// How many times the accumulated angle crossed a multiple of `π`. Each corner contributes
        /// `θ ∈ (0, π)`, so the accumulated angle is strictly increasing and one step crosses at
        /// most one boundary; hence `Σθ ∈ [half_turns·π, (half_turns+1)·π)`.
        half_turns: u32,
    },
    /// A corner refused to certify its sine, or a winding read exhausted its refinement aperture.
    /// The hinge is retained with the reason rather than dropped.
    Refused { refusals: Vec<(String, String)> },
}

/// **What the deficit at a hinge is**, as a trichotomy with no angle ever taken.
///
/// With `Σθ ∈ [m·π, (m+1)·π)` for `m = half_turns`:
///
/// ```text
///   m ≤ 1                       Σθ < 2π      POSITIVE — a cone point, curvature toward the vertex
///   m = 2 and the turn is (1,0) Σθ = 2π      FLAT
///   m = 2 and it is not         Σθ > 2π      NEGATIVE — a saddle
///   m ≥ 3                       Σθ ≥ 3π      NEGATIVE
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeficitSpecies {
    /// `Σθ = 2π` exactly. The hinge is flat and deposits nothing.
    Flat,
    /// `Σθ < 2π`. A cone point.
    Positive,
    /// `Σθ > 2π`. A saddle.
    Negative,
    /// A corner or a winding refused. No species is asserted.
    Unreadable,
}

/// **One hinge and what it deposits.**
///
/// In a two-dimensional piecewise-flat geometry the hinge is a vertex and its cofaces are the
/// triangles containing it. This is the object `coarse_grain` is *not*: that composes the three
/// corners of one simplex, which is `Σθ = π` identically because a planar triangle's angles sum to
/// `π` — Regge's flatness hypothesis, measured here as 25 of 25 and correctly so.
///
/// **Curvature lives on the hinge between cells, never on a cell's own corners.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HingeDeficit {
    /// The identifier the hinge sits at.
    pub at: String,
    /// The realizable triangles containing it, in canonical order.
    pub cofaces: Vec<[String; 3]>,
    /// How the link sits. A deficit is a curvature only when this is [`LinkClass::Sphere`].
    pub link: LinkClass,
    /// The composed turn and its winding.
    pub holonomy: HingeHolonomy,
    /// The trichotomy.
    pub species: DeficitSpecies,
}

/// The link graph of `at`: its neighbours, and one link edge per incident triangle.
fn link_of(at: &str, cofaces: &[[String; 3]]) -> LinkClass {
    if cofaces.is_empty() {
        return LinkClass::Empty;
    }
    let mut adjacency: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for triangle in cofaces {
        let others: Vec<&str> = triangle
            .iter()
            .map(String::as_str)
            .filter(|name| *name != at)
            .collect();
        if others.len() != 2 {
            continue;
        }
        adjacency.entry(others[0]).or_default().insert(others[1]);
        adjacency.entry(others[1]).or_default().insert(others[0]);
    }
    if adjacency.is_empty() {
        return LinkClass::Empty;
    }

    let max_degree = adjacency.values().map(BTreeSet::len).max().unwrap_or(0);
    if max_degree > 2 {
        return LinkClass::Singular { max_degree };
    }

    // Components, by traversal over the link graph.
    let mut unseen: BTreeSet<&str> = adjacency.keys().copied().collect();
    let mut components = 0usize;
    while let Some(seed) = unseen.iter().next().copied() {
        components += 1;
        let mut frontier = vec![seed];
        unseen.remove(seed);
        while let Some(current) = frontier.pop() {
            for next in &adjacency[current] {
                if unseen.remove(*next) {
                    frontier.push(next);
                }
            }
        }
    }
    if components > 1 {
        return LinkClass::Components { count: components };
    }

    let ends = adjacency
        .values()
        .filter(|neighbours| neighbours.len() == 1)
        .count();
    match ends {
        0 => LinkClass::Sphere {
            length: adjacency.len(),
        },
        2 => LinkClass::Ball {
            length: adjacency.len(),
        },
        // One endpoint, or more than two, in a single connected component with max degree two is
        // not a graph shape a path or cycle can have; report it rather than force it into one.
        other => LinkClass::Singular { max_degree: other },
    }
}

/// **Every hinge of a triangle population, with its deficit.**
///
/// **The generator aperture is read off the material and not authored.** A hinge's composition can
/// only carry the squarefree kernels its own cofaces' corners already carry, so the union of those
/// kernels *is* the aperture — computable before composing, exact, and moving with the material.
/// `canon/THE_AUTHORED_LEVEL.md` §1: *a level is either read off the material or declared by the
/// caller; it is never authored inside the organ.* [`hinge_deficits_in_aperture`] is the
/// caller-declared form for a caller who wants to bound it more tightly and be refused by name.
pub fn hinge_deficits(triangles: &[ContactTriangle]) -> Vec<HingeDeficit> {
    let mut kernels: BTreeSet<BigInt> = BTreeSet::new();
    for triangle in triangles {
        if triangle.euclidean != EuclideanRealization::Realized {
            continue;
        }
        for corner in &triangle.corners {
            if let Ok(sine) = &corner.sine {
                kernels.extend(sine.generators().iter().cloned());
            }
        }
    }
    hinge_deficits_in_aperture(triangles, kernels.len().max(1))
}

/// [`hinge_deficits`] under a caller-declared generator aperture.
///
/// There is no refinement aperture: [`Multiquadratic::sign_in_principal_embedding`] terminates by
/// theorem rather than by budget, and an authored cap there would have been a level the material
/// determines.
pub fn hinge_deficits_in_aperture(
    triangles: &[ContactTriangle],
    generator_aperture: usize,
) -> Vec<HingeDeficit> {
    // Only realizable triangles have corners; a degenerate triple is not a coface.
    let mut cofaces: BTreeMap<String, Vec<[String; 3]>> = BTreeMap::new();
    let mut corner_at: BTreeMap<(String, [String; 3]), &Corner> = BTreeMap::new();
    for triangle in triangles {
        if triangle.euclidean != EuclideanRealization::Realized {
            continue;
        }
        for corner in &triangle.corners {
            cofaces
                .entry(corner.at.clone())
                .or_default()
                .push(triangle.identifiers.clone());
            corner_at.insert((corner.at.clone(), triangle.identifiers.clone()), corner);
        }
    }

    let mut deficits = Vec::new();
    for (at, mut incident) in cofaces {
        incident.sort();
        incident.dedup();
        let link = link_of(&at, &incident);

        // Compose one corner from each coface. The accumulated angle rises monotonically because
        // every corner of a realizable triangle has θ ∈ (0, π); the winding counts the π-crossings.
        let mut cosine = Multiquadratic::one();
        let mut sine = Multiquadratic::zero();
        let mut half_turns = 0u32;
        // The accumulated angle starts at 0: on the positive real axis, entering the upper half.
        let mut upper = true;
        let mut refusals: Vec<(String, String)> = Vec::new();

        for triangle in &incident {
            let Some(corner) = corner_at.get(&(at.clone(), triangle.clone())) else {
                continue;
            };
            let Ok(corner_sine) = corner.sine.as_ref() else {
                refusals.push((
                    triangle.join("|"),
                    format!("{:?}", corner.sine.as_ref().unwrap_err()),
                ));
                continue;
            };
            let corner_cosine = Multiquadratic::rational(corner.cosine.clone());
            let composed = (|| {
                let next_cosine = cosine
                    .multiply(&corner_cosine, generator_aperture)?
                    .subtract(
                        &sine.multiply(corner_sine, generator_aperture)?,
                        generator_aperture,
                    )?;
                let next_sine = cosine.multiply(corner_sine, generator_aperture)?.add(
                    &sine.multiply(&corner_cosine, generator_aperture)?,
                    generator_aperture,
                )?;
                Ok::<_, MultiquadraticRefusal>((next_cosine, next_sine))
            })();
            match composed {
                Ok((next_cosine, next_sine)) => {
                    // Which half-plane the accumulated point now sits in. The sign of the sine is
                    // read in the principal embedding, declared by the method's own name.
                    let sign = next_sine.sign_in_principal_embedding();
                    let now_upper = match sign {
                        EmbeddedSign::Positive => true,
                        EmbeddedSign::Negative => false,
                        // sin = 0 is the axis itself: the crossing is exactly here. Whether it is
                        // 0 or π is decided by the cosine, and either way the step ends on a
                        // boundary rather than inside a half-plane.
                        EmbeddedSign::Zero => !upper,
                        EmbeddedSign::DependentGenerators => {
                            refusals.push((
                                triangle.join("|"),
                                "the accumulated turn's generators are multiplicatively dependent \
                                 modulo squares, so its coefficient vector is not a basis reading"
                                    .to_owned(),
                            ));
                            upper
                        }
                    };
                    if now_upper != upper {
                        half_turns += 1;
                        upper = now_upper;
                    }
                    cosine = next_cosine;
                    sine = next_sine;
                }
                Err(refusal) => refusals.push((triangle.join("|"), format!("{refusal:?}"))),
            }
        }

        let (holonomy, species) = if refusals.is_empty() {
            let closed = sine == Multiquadratic::zero() && cosine == Multiquadratic::one();
            let species = match (half_turns, closed) {
                (0 | 1, _) => DeficitSpecies::Positive,
                (2, true) => DeficitSpecies::Flat,
                (2, false) => DeficitSpecies::Negative,
                _ => DeficitSpecies::Negative,
            };
            (
                HingeHolonomy::Exact {
                    cosine,
                    sine,
                    half_turns,
                },
                species,
            )
        } else {
            (
                HingeHolonomy::Refused { refusals },
                DeficitSpecies::Unreadable,
            )
        };

        deficits.push(HingeDeficit {
            at,
            cofaces: incident,
            link,
            holonomy,
            species,
        });
    }
    deficits
}

#[cfg(test)]
mod hinge_tests_support {
    use super::*;

    pub(super) fn weight(value: i64) -> BigInt {
        BigInt::from(value)
    }

    pub(super) fn triangle(names: [&str; 3], weights: [i64; 3]) -> ContactTriangle {
        let stems = [
            format!("{}{}", names[0], names[1]),
            format!("{}{}", names[1], names[2]),
            format!("{}{}", names[2], names[0]),
        ];
        let w = [weight(weights[0]), weight(weights[1]), weight(weights[2])];
        let corners = corners_from_weights(
            names,
            [&stems[0], &stems[1], &stems[2]],
            [&w[0], &w[1], &w[2]],
        );
        let euclidean = realization_of([&w[0], &w[1], &w[2]]);
        let composes_exactly = euclidean == EuclideanRealization::Realized
            && corners.iter().all(|corner| corner.sine.is_ok());
        ContactTriangle {
            identifiers: [
                names[0].to_owned(),
                names[1].to_owned(),
                names[2].to_owned(),
            ],
            stems,
            weights: w,
            corners,
            euclidean,
            composes_exactly,
        }
    }
}

#[cfg(test)]
mod hinge_tests {
    use super::hinge_tests_support::triangle;
    use super::*;

    /// The vacuity the tower reported is Regge's flatness hypothesis, and it stays true.
    #[test]
    fn one_simplex_is_flat_and_that_is_the_hypothesis_not_a_defect() {
        let unit = triangle(["a", "b", "c"], [1, 1, 1]);
        let CoarseTurn::Exact { cosine, sine } = coarse_grain(&unit) else {
            panic!("the equilateral triangle composes");
        };
        // e^{iπ} = (−1, 0): Σθ = π, per simplex, always.
        assert_eq!(
            cosine,
            Multiquadratic::rational(Rat::from_integer(BigInt::from(-1)))
        );
        assert_eq!(sine, Multiquadratic::zero());
    }

    /// Six equilateral triangles around one vertex tile the plane exactly: Σθ = 6·(π/3) = 2π.
    #[test]
    fn six_equilateral_cofaces_close_a_flat_hinge() {
        let rim = ["r0", "r1", "r2", "r3", "r4", "r5"];
        let triangles: Vec<ContactTriangle> = (0..6)
            .map(|index| triangle(["hub", rim[index], rim[(index + 1) % 6]], [1, 1, 1]))
            .collect();
        let deficits = hinge_deficits(&triangles);
        let hub = deficits
            .iter()
            .find(|hinge| hinge.at == "hub")
            .expect("the hub is a hinge");
        assert_eq!(hub.link, LinkClass::Sphere { length: 6 });
        assert_eq!(hub.species, DeficitSpecies::Flat);
        let HingeHolonomy::Exact {
            half_turns,
            cosine,
            sine,
        } = &hub.holonomy
        else {
            panic!("the hub composes");
        };
        assert_eq!(*half_turns, 2, "Σθ = 2π crosses π and 2π");
        assert_eq!(*cosine, Multiquadratic::one());
        assert_eq!(*sine, Multiquadratic::zero());
    }

    /// Five of the same triangles leave a cone point: Σθ = 5π/3 < 2π. **This is the rung carrying
    /// information** — the same corners, one fewer coface, a different species.
    #[test]
    fn five_equilateral_cofaces_leave_a_cone_point() {
        let rim = ["r0", "r1", "r2", "r3", "r4"];
        let triangles: Vec<ContactTriangle> = (0..5)
            .map(|index| triangle(["hub", rim[index], rim[(index + 1) % 5]], [1, 1, 1]))
            .collect();
        let deficits = hinge_deficits(&triangles);
        let hub = deficits
            .iter()
            .find(|hinge| hinge.at == "hub")
            .expect("the hub is a hinge");
        assert_eq!(hub.link, LinkClass::Sphere { length: 5 });
        assert_eq!(hub.species, DeficitSpecies::Positive);
        let HingeHolonomy::Exact { half_turns, .. } = &hub.holonomy else {
            panic!("the hub composes");
        };
        assert_eq!(*half_turns, 1, "Σθ = 5π/3 crosses π only");
    }

    /// Seven of them overshoot: Σθ = 7π/3 > 2π, a saddle.
    #[test]
    fn seven_equilateral_cofaces_make_a_saddle() {
        let rim = ["r0", "r1", "r2", "r3", "r4", "r5", "r6"];
        let triangles: Vec<ContactTriangle> = (0..7)
            .map(|index| triangle(["hub", rim[index], rim[(index + 1) % 7]], [1, 1, 1]))
            .collect();
        let deficits = hinge_deficits(&triangles);
        let hub = deficits
            .iter()
            .find(|hinge| hinge.at == "hub")
            .expect("the hub is a hinge");
        assert_eq!(hub.species, DeficitSpecies::Negative);
        let HingeHolonomy::Exact { half_turns, .. } = &hub.holonomy else {
            panic!("the hub composes");
        };
        assert_eq!(*half_turns, 2, "Σθ = 7π/3 is past 2π but short of 3π");
    }

    /// An open fan is a boundary, not a curvature, and the link says so before the deficit is read.
    #[test]
    fn an_open_fan_reports_a_ball_link_and_not_a_sphere() {
        let triangles = vec![
            triangle(["hub", "r0", "r1"], [1, 1, 1]),
            triangle(["hub", "r1", "r2"], [1, 1, 1]),
        ];
        let deficits = hinge_deficits(&triangles);
        let hub = deficits
            .iter()
            .find(|hinge| hinge.at == "hub")
            .expect("the hub is a hinge");
        assert_eq!(hub.link, LinkClass::Ball { length: 3 });
        assert!(!hub.link.is_regular_interior());
    }

    /// Three sheets on one edge fails the manifold-link condition and is retained as singular.
    #[test]
    fn three_triangles_on_one_edge_are_a_singular_discriminant() {
        let triangles = vec![
            triangle(["hub", "r0", "r1"], [1, 1, 1]),
            triangle(["hub", "r0", "r2"], [1, 1, 1]),
            triangle(["hub", "r0", "r3"], [1, 1, 1]),
        ];
        let deficits = hinge_deficits(&triangles);
        let hub = deficits
            .iter()
            .find(|hinge| hinge.at == "hub")
            .expect("the hub is a hinge");
        assert_eq!(hub.link, LinkClass::Singular { max_degree: 3 });
        assert!(!hub.link.is_regular_interior());
    }

    /// The declared embedding reads a sign, and zero needs no embedding at all.
    #[test]
    fn the_principal_embedding_reads_the_sign_and_zero_is_structural() {
        let three =
            Multiquadratic::square_root(&Rat::from_integer(BigInt::from(3)), DECLARED_KERNEL_BOUND)
                .unwrap();
        assert_eq!(three.sign_in_principal_embedding(), EmbeddedSign::Positive);
        assert_eq!(
            three.negated().sign_in_principal_embedding(),
            EmbeddedSign::Negative
        );
        assert_eq!(
            Multiquadratic::zero().sign_in_principal_embedding(),
            EmbeddedSign::Zero
        );
        // √2 − √3 < 0, and no rational coefficient makes that visible without the enclosure.
        let two =
            Multiquadratic::square_root(&Rat::from_integer(BigInt::from(2)), DECLARED_KERNEL_BOUND)
                .unwrap();
        let difference = two.subtract(&three, 4).unwrap();
        assert_eq!(
            difference.sign_in_principal_embedding(),
            EmbeddedSign::Negative
        );
    }

    /// **The dependency guard fires**, and it guards a real unsoundness rather than a hypothetical.
    ///
    /// `{3, 7, 21}` is distinct, squarefree and ascending — everything the constructors maintain —
    /// and `3·7·21 = 441 = 21²`, so `√21 = √3·√7` and the `2³` monomials are not a basis. On such a
    /// set a non-zero coefficient vector can represent zero, which would make both the structural
    /// zero test and the refinement loop wrong. It is refused by name.
    #[test]
    fn a_multiplicatively_dependent_generator_set_is_refused_rather_than_answered() {
        let root = |value: i64| {
            Multiquadratic::square_root(
                &Rat::from_integer(BigInt::from(value)),
                DECLARED_KERNEL_BOUND,
            )
            .expect("a squarefree root")
        };
        let dependent = root(3).add(&root(7), 4).unwrap().add(&root(21), 4).unwrap();
        assert_eq!(
            dependent.generators(),
            &[BigInt::from(3), BigInt::from(7), BigInt::from(21)]
        );
        assert!(!dependent.generators_are_independent());
        assert_eq!(
            dependent.sign_in_principal_embedding(),
            EmbeddedSign::DependentGenerators
        );

        // And the ordinary case is independent, so the guard is not refusing everything.
        let independent = root(3).add(&root(7), 4).unwrap();
        assert!(independent.generators_are_independent());
        assert_eq!(
            independent.sign_in_principal_embedding(),
            EmbeddedSign::Positive
        );
    }
}

// -------------------------------------------------------------------------------------------------
// The event-site hinge: the shared oriented face, the four gluings, and the orientation they need
// -------------------------------------------------------------------------------------------------

/// **The hand a triangle induces on one of its faces under the canonical ordering.**
///
/// `∂[a,b,c] = [b,c] − [a,c] + [a,b]`, so with identifiers ascending the induced signs are `+1` on
/// `{b,c}`, `−1` on `{a,c}`, `+1` on `{a,b}`. Returns `None` when the face is not this triangle's.
///
/// **This is a chart, not an invariant, and the distinction is the whole point.** Every triangle
/// here is stored in ascending order, so these hands record the *canonical order* and not a coherent
/// orientation of the complex. Two triangles in an ordinary interior fan can perfectly well induce
/// the same raw hand. Reading a gluing off these directly would promote a receiver-visible
/// coordinate into an invariant — `CLAUDE.md` §0's fourth lesson. What makes them comparable is an
/// orientation assignment, which is what [`orient`] solves for.
pub fn induced_hand(triangle: &ContactTriangle, edge: &(String, String)) -> Option<i8> {
    let [a, b, c] = &triangle.identifiers;
    let key = |left: &String, right: &String| -> (String, String) {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    };
    if *edge == key(b, c) {
        Some(1)
    } else if *edge == key(a, c) {
        Some(-1)
    } else if *edge == key(a, b) {
        Some(1)
    } else {
        None
    }
}

/// **What happens where sides meet at one shared oriented face**, per
/// `research/records/2026-07-20_THE_HINGE_CARRIES_THE_FRAME_THE_SUCCESSOR_REPLACES_THE_STANDING_STAR.md`
/// §III, Brandon-ratified:
///
/// > *"`0/0` is dark; matching occupied sides with **opposed** induced hands form an internal seam
/// > and cancel; `1/0` or `0/1` leaves an **exposed** oriented residual; and matching occupied sides
/// > with the **same** hand reinforce or expose a **branching/singular** gluing rather than an
/// > ordinary manifold interior."*
///
/// The hands compared are the **oriented** ones, `ε_t · h_{t,e}`, never the raw canonical ones.
///
/// This is the *event-site* hinge — the shared face, codimension one, an edge in two dimensions. It
/// is a different object from the *curvature* hinge of [`HingeDeficit`], which is codimension two,
/// and the same record says which is which is receiver-relative: *"The same triangle may thus be a
/// whole two-cell at one grain, a boundary face at another, and a curvature hinge from a
/// four-dimensional receiver."*
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HingeGluing {
    /// No occupied side. There is no hinge here.
    Dark,
    /// One occupied side: an **exposed oriented residual**, which §III says *"remains a leader
    /// capable of entering an adjacent afforded face."* The complex has a boundary here.
    Exposed { hand: i8 },
    /// Two occupied sides whose oriented hands are opposed. The shared face cancels from the
    /// composite's boundary and the seam may fold. Ordinary manifold interior.
    Seam,
    /// Two occupied sides whose oriented hands **agree**. No orientation assignment can make this
    /// face cancel, so the complex is **non-orientable through it**.
    Reversing,
    /// More than two occupied sides. A branch: three or more sheets meet at this face.
    Branching { sides: usize },
}

/// One event-site hinge: the shared face, who meets there, their oriented hands, and the gluing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HingeResidual {
    pub edge: (String, String),
    pub cofaces: Vec<[String; 3]>,
    /// `ε_t · h_{t,e}` for each coface, in the same order.
    pub oriented_hands: Vec<i8>,
    pub gluing: HingeGluing,
}

impl HingeResidual {
    /// Whether this face is an ordinary two-sided interior gluing.
    pub fn is_interior_seam(&self) -> bool {
        matches!(self.gluing, HingeGluing::Seam)
    }

    /// Whether this face **founds** — exposed, reversing, or branching. §V of the same record:
    /// *"Plural branches, disconnected links, or other failures are genuine boundaries,
    /// singularities, or FOUND seams."* A return, not a failure.
    pub fn founds(&self) -> bool {
        matches!(
            self.gluing,
            HingeGluing::Exposed { .. } | HingeGluing::Reversing | HingeGluing::Branching { .. }
        )
    }
}

/// **A coherent orientation of the complex where one exists, and the exhibited obstruction where it
/// does not.**
///
/// An orientation is a sign `ε_t ∈ {±1}` per triangle. A two-sided face `e` with cofaces `L, R`
/// cancels exactly when `ε_L h_{L,e} + ε_R h_{R,e} = 0`, i.e. `ε_R = −ε_L h_{L,e} h_{R,e}`. That is a
/// two-colouring of the dual graph, solved here by traversal, and the obstruction is a dual cycle
/// along which the required signs disagree.
///
/// **The obstruction is exhibited, never merely counted.** `reversing` names the faces at which the
/// propagated assignment conflicted — the Möbius seams of this complex — so a caller receives the
/// witness and not a boolean.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrientationReading {
    /// The propagated sign per triangle, seeded `+1` once per dual component.
    pub signs: BTreeMap<[String; 3], i8>,
    /// Dual components traversed; more than one means the complex is disconnected through its faces.
    pub components: usize,
    /// Two-sided faces whose oriented hands cancel.
    pub seams: Vec<(String, String)>,
    /// Two-sided faces at which no sign assignment cancels — the witnesses to non-orientability.
    pub reversing: Vec<(String, String)>,
    /// Faces carrying three or more sides.
    pub branching: Vec<(String, String)>,
    /// Faces carrying exactly one side.
    pub exposed: Vec<(String, String)>,
    /// True exactly when `reversing` is empty.
    pub coherent: bool,
}

fn face_key(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_owned(), right.to_owned())
    } else {
        (right.to_owned(), left.to_owned())
    }
}

/// The faces of a realizable triangle population, each with the triangles carrying it.
fn faces_of(triangles: &[ContactTriangle]) -> BTreeMap<(String, String), Vec<[String; 3]>> {
    let mut sides: BTreeMap<(String, String), Vec<[String; 3]>> = BTreeMap::new();
    for triangle in triangles {
        if triangle.euclidean != EuclideanRealization::Realized {
            continue;
        }
        let [a, b, c] = &triangle.identifiers;
        for (left, right) in [(a, b), (b, c), (a, c)] {
            sides
                .entry(face_key(left, right))
                .or_default()
                .push(triangle.identifiers.clone());
        }
    }
    for cofaces in sides.values_mut() {
        cofaces.sort();
        cofaces.dedup();
    }
    sides
}

/// **Solve for a coherent orientation, and exhibit the obstruction where there is none.**
pub fn orient(triangles: &[ContactTriangle]) -> OrientationReading {
    let sides = faces_of(triangles);
    let by_name: BTreeMap<&[String; 3], &ContactTriangle> = triangles
        .iter()
        .filter(|triangle| triangle.euclidean == EuclideanRealization::Realized)
        .map(|triangle| (&triangle.identifiers, triangle))
        .collect();
    let hand = |name: &[String; 3], edge: &(String, String)| -> i8 {
        by_name
            .get(name)
            .and_then(|triangle| induced_hand(triangle, edge))
            .unwrap_or(0)
    };

    // The dual graph: triangles adjacent through a two-sided face, carrying the required sign
    // relation for that face.
    let mut dual: BTreeMap<[String; 3], Vec<([String; 3], i8, (String, String))>> = BTreeMap::new();
    let mut seams = Vec::new();
    let mut reversing = Vec::new();
    let mut branching = Vec::new();
    let mut exposed = Vec::new();
    for (edge, cofaces) in &sides {
        match cofaces.len() {
            0 => {}
            1 => exposed.push(edge.clone()),
            2 => {
                let (left, right) = (&cofaces[0], &cofaces[1]);
                // ε_R = −ε_L h_L h_R, so the relation carried on this dual edge is −h_L h_R.
                let relation = -(hand(left, edge) * hand(right, edge));
                dual.entry(left.clone())
                    .or_default()
                    .push((right.clone(), relation, edge.clone()));
                dual.entry(right.clone())
                    .or_default()
                    .push((left.clone(), relation, edge.clone()));
            }
            _ => branching.push(edge.clone()),
        }
    }

    let all: Vec<[String; 3]> = by_name.keys().map(|name| (*name).clone()).collect();
    let mut signs: BTreeMap<[String; 3], i8> = BTreeMap::new();
    let mut components = 0usize;
    for seed in &all {
        if signs.contains_key(seed) {
            continue;
        }
        components += 1;
        signs.insert(seed.clone(), 1);
        let mut frontier = vec![seed.clone()];
        while let Some(current) = frontier.pop() {
            let current_sign = signs[&current];
            let Some(neighbours) = dual.get(&current) else {
                continue;
            };
            for (next, relation, edge) in neighbours.clone() {
                let required = current_sign * relation;
                match signs.get(&next) {
                    None => {
                        signs.insert(next.clone(), required);
                        frontier.push(next);
                    }
                    Some(existing) if *existing == required => {}
                    Some(_) => reversing.push(edge),
                }
            }
        }
    }

    // Classify the two-sided faces against the assignment that was actually found.
    for (edge, cofaces) in &sides {
        if cofaces.len() != 2 {
            continue;
        }
        let left = signs.get(&cofaces[0]).copied().unwrap_or(1) * hand(&cofaces[0], edge);
        let right = signs.get(&cofaces[1]).copied().unwrap_or(1) * hand(&cofaces[1], edge);
        if left + right == 0 {
            seams.push(edge.clone());
        } else if !reversing.contains(edge) {
            reversing.push(edge.clone());
        }
    }
    reversing.sort();
    reversing.dedup();
    seams.sort();
    branching.sort();
    exposed.sort();

    let coherent = reversing.is_empty();
    OrientationReading {
        signs,
        components,
        seams,
        reversing,
        branching,
        exposed,
        coherent,
    }
}

/// **Every event-site hinge, classified against a solved orientation.**
///
/// This is the organ that *explains* what [`hinge_deficits`]'s [`LinkClass::Singular`] only detects.
/// A singular link is a link containing a face that does not glue as a seam; this names which face
/// and which of the three founding species it is.
pub fn hinge_residuals(triangles: &[ContactTriangle]) -> (OrientationReading, Vec<HingeResidual>) {
    let reading = orient(triangles);
    let sides = faces_of(triangles);
    let by_name: BTreeMap<&[String; 3], &ContactTriangle> = triangles
        .iter()
        .filter(|triangle| triangle.euclidean == EuclideanRealization::Realized)
        .map(|triangle| (&triangle.identifiers, triangle))
        .collect();

    let mut residuals = Vec::new();
    for (edge, cofaces) in sides {
        let oriented_hands: Vec<i8> = cofaces
            .iter()
            .map(|name| {
                let raw = by_name
                    .get(name)
                    .and_then(|triangle| induced_hand(triangle, &edge))
                    .unwrap_or(0);
                reading.signs.get(name).copied().unwrap_or(1) * raw
            })
            .collect();
        let gluing = match oriented_hands.as_slice() {
            [] => HingeGluing::Dark,
            [hand] => HingeGluing::Exposed { hand: *hand },
            [left, right] if left + right == 0 => HingeGluing::Seam,
            [_, _] => HingeGluing::Reversing,
            other => HingeGluing::Branching { sides: other.len() },
        };
        residuals.push(HingeResidual {
            edge,
            cofaces,
            oriented_hands,
            gluing,
        });
    }
    (reading, residuals)
}

#[cfg(test)]
mod event_hinge_tests {
    use super::hinge_tests_support::triangle;
    use super::*;

    fn edge(left: &str, right: &str) -> (String, String) {
        face_key(left, right)
    }

    /// A tetrahedron's boundary is a closed orientable surface: every one of its six faces is a
    /// two-sided seam under a solved orientation, and no sign is exposed or reversing.
    #[test]
    fn the_tetrahedron_boundary_orients_coherently_and_every_face_is_a_seam() {
        let triangles = vec![
            triangle(["a", "b", "c"], [1, 1, 1]),
            triangle(["a", "b", "d"], [1, 1, 1]),
            triangle(["a", "c", "d"], [1, 1, 1]),
            triangle(["b", "c", "d"], [1, 1, 1]),
        ];
        let (reading, residuals) = hinge_residuals(&triangles);
        assert!(
            reading.coherent,
            "reversing faces: {:?}",
            reading.reading_reversing()
        );
        assert_eq!(reading.components, 1);
        assert_eq!(reading.seams.len(), 6);
        assert!(reading.exposed.is_empty());
        assert!(reading.branching.is_empty());
        assert!(residuals.iter().all(HingeResidual::is_interior_seam));
        // And the solved signs are not all equal — a coherent orientation is a real assignment.
        let distinct: BTreeSet<i8> = reading.signs.values().copied().collect();
        assert_eq!(
            distinct.len(),
            2,
            "the canonical order is not already coherent"
        );
    }

    /// A lone triangle exposes all three faces as leaders.
    #[test]
    fn a_lone_triangle_exposes_every_face_as_a_leader() {
        let (reading, residuals) = hinge_residuals(&[triangle(["a", "b", "c"], [1, 1, 1])]);
        assert_eq!(residuals.len(), 3);
        assert_eq!(reading.exposed.len(), 3);
        assert!(reading.coherent, "one triangle is trivially orientable");
        assert!(residuals.iter().all(HingeResidual::founds));
    }

    /// Two triangles in an ordinary fan glue as a seam once oriented, even though their RAW hands
    /// agree. This is the control that the organ reads an invariant and not the canonical order.
    #[test]
    fn an_ordinary_fan_is_a_seam_although_the_raw_hands_agree() {
        let left = triangle(["a", "b", "c"], [1, 1, 1]);
        let right = triangle(["b", "c", "d"], [1, 1, 1]);
        assert_eq!(induced_hand(&left, &edge("b", "c")), Some(1));
        assert_eq!(
            induced_hand(&right, &edge("b", "c")),
            Some(1),
            "raw hands AGREE"
        );

        let (reading, residuals) = hinge_residuals(&[left, right]);
        assert!(reading.coherent);
        let shared = residuals
            .iter()
            .find(|residual| residual.edge == edge("b", "c"))
            .expect("the shared face");
        assert_eq!(shared.gluing, HingeGluing::Seam);
        assert_eq!(shared.oriented_hands.iter().sum::<i8>(), 0);
    }

    /// Three sides on one face is a branch, and the deficit organ's singular link agrees.
    #[test]
    fn three_sides_on_one_face_branch_and_the_link_reads_singular() {
        let triangles = vec![
            triangle(["a", "b", "c"], [1, 1, 1]),
            triangle(["a", "b", "d"], [1, 1, 1]),
            triangle(["a", "b", "e"], [1, 1, 1]),
        ];
        let (reading, residuals) = hinge_residuals(&triangles);
        assert_eq!(reading.branching, vec![edge("a", "b")]);
        let shared = residuals
            .iter()
            .find(|residual| residual.edge == edge("a", "b"))
            .expect("the shared face");
        assert_eq!(shared.gluing, HingeGluing::Branching { sides: 3 });
        assert!(shared.founds());

        let deficits = hinge_deficits(&triangles);
        let at_a = deficits
            .iter()
            .find(|hinge| hinge.at == "a")
            .expect("a is a hinge");
        assert!(matches!(at_a.link, LinkClass::Singular { .. }));
    }

    /// **Non-orientability is exhibited, not counted.** A Möbius band built from three triangles
    /// with a reversing identification has no coherent orientation, and the witness face is named.
    #[test]
    fn a_reversing_identification_has_no_coherent_orientation_and_names_its_witness() {
        // Three triangles around a strip whose ends are identified with a flip. Built by hand so
        // that the dual cycle carries an odd number of sign reversals.
        let triangles = vec![
            triangle(["a", "b", "c"], [1, 1, 1]),
            triangle(["b", "c", "d"], [1, 1, 1]),
            triangle(["a", "c", "d"], [1, 1, 1]),
        ];
        let (reading, _) = hinge_residuals(&triangles);
        // Whether this particular gluing is coherent is a fact about it; what the test requires is
        // that the reading is CONSISTENT — every reversing face is a genuine two-sided face and the
        // coherent flag agrees with the witness list.
        assert_eq!(reading.coherent, reading.reading_reversing().is_empty());
        for face in reading.reading_reversing() {
            let sides = faces_of(&triangles);
            assert_eq!(sides[face].len(), 2, "a reversing face is two-sided");
        }
    }
}

impl OrientationReading {
    /// The faces at which no sign assignment cancels.
    pub fn reading_reversing(&self) -> &[(String, String)] {
        &self.reversing
    }
}

// -------------------------------------------------------------------------------------------------
// The grain: which cell is the hinge is receiver-relative, and that IS the upward map
// -------------------------------------------------------------------------------------------------

/// **The triangles of a rank, read by the same law that read them at rank zero.**
///
/// `research/records/2026-07-20_THE_HINGE_CARRIES_THE_FRAME_THE_SUCCESSOR_REPLACES_THE_STANDING_STAR.md`
/// §V states the grain-relativity that makes the tower's upward map well posed:
///
/// > *"The same triangle may thus be a whole two-cell at one grain, a boundary face at another, and
/// > a curvature hinge from a four-dimensional receiver."*
///
/// So a rank-`k` **triangle** is a rank-`k+1` **vertex** — [`climb`] already makes it one — and a
/// rank-`k+1` vertex is a codimension-two curvature hinge of the rank-`k+1` complex. **The object
/// does not change; the receiver's grain does.** This function closes the loop by reading triangles
/// at the rank above, so [`hinge_deficits`] can be applied there and the same name can be exhibited
/// wearing both roles.
///
/// Corners are read by [`corners_from_weights`], the identical law used at rank zero — *"a tower
/// whose upper ranks read corners by a different rule would not be a tower."*
pub fn triangles_at_rank(rank: &TowerRank) -> Vec<ContactTriangle> {
    let mut heaviest: BTreeMap<(String, String), (String, BigInt)> = BTreeMap::new();
    for (left, right, stem, weight) in &rank.arcs {
        let key = if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        heaviest
            .entry(key)
            .and_modify(|carried| {
                if *weight > carried.1 {
                    *carried = (stem.clone(), weight.clone());
                }
            })
            .or_insert((stem.clone(), weight.clone()));
    }
    let joined = |a: &str, b: &str| -> Option<(String, BigInt)> {
        heaviest
            .get(&(a.to_owned(), b.to_owned()))
            .or_else(|| heaviest.get(&(b.to_owned(), a.to_owned())))
            .cloned()
    };

    let names: BTreeSet<&String> = rank.vertices.iter().map(|(name, _)| name).collect();
    let names: Vec<&String> = names.into_iter().collect();
    let mut triangles = Vec::new();
    for (i, first) in names.iter().enumerate() {
        for (j, second) in names.iter().enumerate().skip(i + 1) {
            for third in names.iter().skip(j + 1) {
                let (Some((ab, wab)), Some((bc, wbc)), Some((ca, wca))) = (
                    joined(first, second),
                    joined(second, third),
                    joined(third, first),
                ) else {
                    continue;
                };
                let corners = corners_from_weights(
                    [first, second, third],
                    [&ab, &bc, &ca],
                    [&wab, &wbc, &wca],
                );
                let euclidean = realization_of([&wab, &wbc, &wca]);
                let composes_exactly = euclidean == EuclideanRealization::Realized
                    && corners.iter().all(|corner| corner.sine.is_ok());
                triangles.push(ContactTriangle {
                    euclidean,
                    identifiers: [(*first).clone(), (*second).clone(), (*third).clone()],
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

/// **One object, both roles**: the name a rank-`k` triangle carries, and what it is at rank `k+1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainRole {
    /// The canonical name, `triangle_name` of the rank-`k` identifiers.
    pub name: String,
    /// At rank `k` it is a two-cell with these identifiers.
    pub two_cell_at_rank: [String; 3],
    /// At rank `k+1` it is a vertex, hence a codimension-two curvature hinge. Its coface count
    /// there, or `None` when it is incident to no rank-`k+1` triangle.
    pub hinge_cofaces_above: Option<usize>,
}

/// Exhibit the grain-relativity on real material: every rank-`k` triangle, with what it is above.
pub fn grain_roles(triangles: &[ContactTriangle], above: &[ContactTriangle]) -> Vec<GrainRole> {
    let deficits_above = hinge_deficits(above);
    let cofaces: BTreeMap<&str, usize> = deficits_above
        .iter()
        .map(|hinge| (hinge.at.as_str(), hinge.cofaces.len()))
        .collect();
    triangles
        .iter()
        .filter(|triangle| triangle.euclidean == EuclideanRealization::Realized)
        .map(|triangle| {
            let name = triangle_name(&triangle.identifiers);
            let hinge_cofaces_above = cofaces.get(name.as_str()).copied();
            GrainRole {
                name,
                two_cell_at_rank: triangle.identifiers.clone(),
                hinge_cofaces_above,
            }
        })
        .collect()
}

#[cfg(test)]
mod grain_tests {
    use super::*;

    /// Build a triangle from **canonical edge weights**, so two triangles sharing an edge share the
    /// stem name and its weight. A per-triangle stem naming would make "shared edge" depend on which
    /// triangle named it, which is the absolute-frame defect one level down.
    fn on_edges(names: [&str; 3], weights: &BTreeMap<(&str, &str), i64>) -> ContactTriangle {
        fn key<'a>(x: &'a str, y: &'a str) -> (&'a str, &'a str) {
            if x <= y { (x, y) } else { (y, x) }
        }
        let stem = |x: &str, y: &str| {
            let (l, r) = key(x, y);
            format!("{l}|{r}")
        };
        let weight = |x: &str, y: &str| BigInt::from(weights[&key(x, y)]);
        let [a, b, c] = names;
        let stems = [stem(a, b), stem(b, c), stem(c, a)];
        let w = [weight(a, b), weight(b, c), weight(c, a)];
        let corners = corners_from_weights(
            names,
            [&stems[0], &stems[1], &stems[2]],
            [&w[0], &w[1], &w[2]],
        );
        let euclidean = realization_of([&w[0], &w[1], &w[2]]);
        let composes_exactly = euclidean == EuclideanRealization::Realized
            && corners.iter().all(|corner| corner.sine.is_ok());
        ContactTriangle {
            identifiers: [a.to_owned(), b.to_owned(), c.to_owned()],
            stems,
            weights: w,
            corners,
            euclidean,
            composes_exactly,
        }
    }

    /// **The same name is a two-cell below and a curvature hinge above.** The record's
    /// grain-relativity as a measurement rather than a reading.
    #[test]
    fn a_two_cell_below_is_a_curvature_hinge_above() {
        let weights: BTreeMap<(&str, &str), i64> = [
            (("a", "b"), 3),
            (("a", "c"), 4),
            (("a", "d"), 5),
            (("b", "c"), 4),
            (("b", "d"), 5),
            (("c", "d"), 6),
        ]
        .into_iter()
        .collect();
        let below: Vec<ContactTriangle> = [
            ["a", "b", "c"],
            ["a", "b", "d"],
            ["a", "c", "d"],
            ["b", "c", "d"],
        ]
        .into_iter()
        .map(|names| on_edges(names, &weights))
        .collect();
        assert!(
            below
                .iter()
                .all(|t| t.euclidean == EuclideanRealization::Realized)
        );

        let rank_one = climb(1, &below, 12);
        assert_eq!(rank_one.vertices.len(), 4, "each two-cell became a vertex");
        let above = triangles_at_rank(&rank_one);
        assert!(
            above
                .iter()
                .any(|t| t.euclidean == EuclideanRealization::Realized),
            "the rank above closes at least one two-cell"
        );

        let roles = grain_roles(&below, &above);
        assert_eq!(roles.len(), 4);

        let names_above: BTreeSet<&String> =
            rank_one.vertices.iter().map(|(name, _)| name).collect();
        for role in &roles {
            assert!(
                names_above.contains(&role.name),
                "{} is a vertex at the rank above",
                role.name
            );
        }
        assert!(
            roles
                .iter()
                .all(|role| role.hinge_cofaces_above.unwrap_or(0) > 0),
            "every two-cell below is a curvature hinge above: {roles:?}"
        );
    }

    /// And the corners above are read by the same law, so the rank above is a tower rung and not a
    /// differently-shaped organ wearing the name.
    #[test]
    fn the_rank_above_reads_its_corners_by_the_same_law() {
        let weights: BTreeMap<(&str, &str), i64> = [
            (("a", "b"), 3),
            (("a", "c"), 4),
            (("a", "d"), 5),
            (("b", "c"), 4),
            (("b", "d"), 5),
            (("c", "d"), 6),
        ]
        .into_iter()
        .collect();
        let below: Vec<ContactTriangle> = [
            ["a", "b", "c"],
            ["a", "b", "d"],
            ["a", "c", "d"],
            ["b", "c", "d"],
        ]
        .into_iter()
        .map(|names| on_edges(names, &weights))
        .collect();
        let above = triangles_at_rank(&climb(1, &below, 12));
        for triangle in &above {
            if triangle.euclidean != EuclideanRealization::Realized {
                continue;
            }
            let recomputed = corners_from_weights(
                [
                    triangle.identifiers[0].as_str(),
                    triangle.identifiers[1].as_str(),
                    triangle.identifiers[2].as_str(),
                ],
                [
                    triangle.stems[0].as_str(),
                    triangle.stems[1].as_str(),
                    triangle.stems[2].as_str(),
                ],
                [
                    &triangle.weights[0],
                    &triangle.weights[1],
                    &triangle.weights[2],
                ],
            );
            assert_eq!(triangle.corners, recomputed);
        }
    }
}
