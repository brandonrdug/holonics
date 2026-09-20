//! **The topological receiver: persistence over the exact aperture filtration, and linking
//! where an embedding exists.**
//!
//! [definition] This is receiver **R5** of
//! `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md` and the topological share of
//! **B7** in `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`: *loops, cycles,
//! linking and writhe where an embedding exists, contact-community persistence, connected
//! components, cavities and entanglement*, with the discipline that **knot-like structure is
//! claimed only where cycles, linking, holonomy or nontrivial gluing actually exist.**
//!
//! Three things are owned here, in this order.
//!
//! # 1. The aperture filtration, and why its order can be `Open`
//!
//! [definition] `crate::physical_constraint_complex` founds incidence by comparing an **exact
//! squared-distance interval** against a declared aperture: `D.upper ≤ a` is `Inside`,
//! `D.lower > a` is `Outside`, and an interval straddling the aperture stays `Open`. Sweeping the
//! aperture instead of fixing it turns that trichotomy into a *filtration*: the entry value of a
//! 1-cell is its exact squared-distance interval, the entry value of a higher simplex is the
//! componentwise maximum over its edges, and every vertex enters at zero. This is the
//! Vietoris–Rips filtration of the presented occurrences, taken over exact squared distances so
//! that **no comparison anywhere below is a float comparison**.
//!
//! [definition] The filtration *order* is decided by exact comparison of those intervals, and it
//! can fail to be decided. For two entry intervals `D₁`, `D₂`:
//!
//! - `D₁.upper < D₂.lower` — decided, `D₁` strictly first;
//! - `D₁ = D₂` — an **exact tie**: one filtration level holding two cells, resolved by the
//!   declared secondary key (grade, then address) and retained by name in
//!   [`ApertureFiltration::exact_ties`];
//! - otherwise the intervals overlap without coinciding — the order is **`Open`**, and it is not
//!   tie-broken. [`open_order_pairs`] returns every such pair with both intervals, and the
//!   persistence reading becomes a **family** over the admissible linear extensions:
//!   [`OrderLaw::ByLowerBound`] and [`OrderLaw::ByUpperBound`] are two of them and are
//!   constructed as the bounds of that indexing, [`OrderLaw::Declared`] takes any third and
//!   **refuses** one that contradicts a decided comparison.
//!
//! An interval entry value can only arise from an interval *position*. A presentation whose
//! coordinate boxes are points has a determinate order up to exact ties
//! ([`ApertureFiltration::order_is_determinate`]), and that is the ordinary case for deposited
//! coordinates, which are exact decimals.
//!
//! # 2. Persistence over a declared field, with integral torsion beside it
//!
//! [proved-standard; implemented-exact] [`persistence`] runs the standard reduction of the
//! filtered boundary matrix — for each column, add earlier columns until its lowest nonzero row
//! is unclaimed — over a **declared** field: `ℚ` exactly, or `𝔽_p` for a declared prime `p`.
//! Births, deaths, essential classes, and therefore connected components (grade 0), cycles
//! (grade 1) and cavities (grade 2) come out with **exact** birth and death values, never a
//! decimal.
//!
//! [definition] The reduction sees one field at a time, so a field-dependent answer would be
//! invisible from inside it. It is made visible from outside: [`integral_profile`] reads the
//! **integral** invariants of the sublevel complex at declared apertures through
//! `crate::rebase_invariants`'s Smith normal form, so the torsion coefficients are returned, and
//! [`TorsionProfile::field_dependence_primes`] names the primes at which `𝔽_p` homology must
//! differ from `ℚ` homology. A reading over one field with no torsion beside it is a reading
//! whose field-dependence was hidden.
//!
//! [definition] Because a sublevel set at aperture `a` is itself decided by the `Inside`/`Open`/
//! `Outside` trichotomy, [`sublevel_family`] returns **two** supports — refusing every `Open`
//! cell and admitting every `Open` cell — and [`integral_profile`] reads both. Both are closed
//! under boundary, because the entry value of a face never exceeds the entry value of a cell it
//! bounds.
//!
//! [implemented-exact] [`community_persistence`] is the grade-0 reading with the presented
//! components retained: at which **exact** squared aperture two presented chains first belong to
//! one contact community. It is computed by an elder-rule union–find rather than by the matrix
//! reduction, and [`grade_zero_agreement`] is the **library** reading that computes both and
//! **refuses** — [`TopologicalError::GradeZeroReadingsDisagree`] — when the grade-0 death multiset
//! and the merge multiset part. The agreement is therefore enforced where the readings are taken
//! and not only where they are tested, so the two computations are a cross-check rather than one
//! computation reported twice.
//!
//! # 3. Linking and writhe, where an embedding exists
//!
//! [proved-standard; implemented-exact] A closed polygonal curve with exact rational vertices and
//! a declared rational projection direction `w` give a genuine diagram: the projection is
//! `x ↦ (⟨u,x⟩, ⟨v,x⟩)` for `u = w × e`, `v = w × u` — both rational, both orthogonal to `w` — and
//! the height is `⟨w,x⟩`. A crossing sign is `ε = sgn det[t_over, t_under, w]`, the classical
//! convention, and every quantity in it is an exact rational.
//!
//! [definition] **Degenerate projections are refused, never perturbed.** A segment parallel to
//! `w`, two projected segments collinear and overlapping, a crossing at a segment endpoint, and
//! two strands at equal height where their projections meet are each returned as a typed
//! [`ProjectionDegeneracy`] naming the curves, the segments and the degeneracy. A perturbation
//! would replace the presented structure with a nearby one and report the answer for the
//! substitute.
//!
//! [proved-standard] The **linking number** is returned as an exact integer by counting the
//! crossings at which the first curve passes over the second. That count equals the count at
//! which the second passes over the first — classically, and it is **checked at every reading**,
//! with [`TopologicalError::LinkingHalvesDisagree`] naming both values if it ever fails — and
//! twice it is the total signed crossing count. `lk(a,b) = lk(b,a)` holds because the crossing
//! population and its signs do not depend on which curve is named first. Invariance under a
//! change of admissible projection direction is tested as an invariant across a declared
//! candidate family by [`linking_under_directions`].
//!
//! [counterexample] **The writhe is not an integer invariant and none is claimed.** What is
//! returned is the *projected* writhe: the signed self-crossing count of one closed polygon under
//! one declared direction, an exact integer for that direction and nothing more. The averaged
//! writhe — the mean of that count over the sphere of directions — is a real number, is not
//! computed here, and is not claimed. `the_projected_writhe_is_not_projection_invariant` exhibits
//! one polygon and two admissible directions whose projected writhes differ, so the distinction
//! is a measured fact of this module and not a caveat.
//!
//! [definition] A **contact loop** is a backbone segment closed by a contact: the chain steps
//! `i → i+1 → … → j` together with the contact 1-cell `(i,j)` form a closed polygon.
//! [`contact_loops`] returns them from the filtration, [`presented_contact_loops`] from the
//! presentation's own within-component contact family with the filtration held to agreement, and
//! the entanglement of two of them is an honest linking reading between two curves that the
//! structure actually carries.
//!
//! # The claim discipline
//!
//! [definition] When the structure a reading needs is absent, the return is a **typed refusal**
//! naming what is missing, never a zero:
//!
//! - [`TopologicalError::NoEmbedding`] — a presented position is a coordinate box with width. An
//!   interval position admits no curve, so no linking, writhe or crossing question is asked of it.
//!   The filtration still runs: persistence needs only the exact interval comparisons.
//! - [`TopologicalError::NoCycle`] — no contact closes any chain segment, so there is no loop to
//!   read. A zero linking number here would be a claim about a curve that does not exist.
//! - [`TopologicalError::NoLink`] — fewer than two vertex-disjoint loops, so no entanglement
//!   question is posed.
//!
//! [`knot_like_reading`] is the gate: it returns a [`KnotLikeWitness`] only where a 1-cycle, a
//! nonzero linking number or a nontrivial contact loop actually exists, and one of the three
//! refusals otherwise.
//!
//! # Formal owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/TopologicalReceiver.lean`, namespace
//! `Soma.Holonics.Foundation.TopologicalReceiver`. The correspondence, both directions:
//!
//! | Rust | Lean |
//! |---|---|
//! | [`ApertureFiltration`] as a monotone family of closed supports | `Filtration`, `Filtration.mono` |
//! | the filtration read as a `ContinuingTower.Tower` | `Filtration.toTower` on the **order dual**, `toTower_restrict` |
//! | [`FiltrationOrder`] validity — every face earlier than its cofaces | `Filtration.FaceClosed` |
//! | induced maps on homology are functorial | `PersistenceModule`, `PersistenceModule.map_id`, `PersistenceModule.map_comp` |
//! | [`persistent_rank`] | `PersistenceModule.persistentRank` |
//! | persistent ranks shrink along the order | `PersistenceModule.persistentRank_le_left`, `PersistenceModule.persistentRank_le_right` |
//! | the pairing is determined by the persistent ranks | `multiplicity_eq`, `multiplicity_eq_of_rank_eq`, `bornAt_eq_of_rank_eq` (the elder-rule pairing uniqueness this file can prove) |
//! | [`Crossing`] and its sign | `Crossing`, `Crossing.sign` |
//! | [`LinkingReading::total_signed`] | `linkingTotal` |
//! | `lk(a,b) = lk(b,a)` | `linkingTotal_comm` |
//! | the over-count and the under-count partition the total | `linkingOver_add_linkingUnder` |
//! | [`TopologicalError::LinkingHalvesDisagree`] cannot fire classically | `HalvesAgree`, `linking_is_an_integer` |
//! | invariance under `w ↦ −w` and under positive scaling | `Crossing.sign_neg_direction`, `Crossing.sign_smul_direction`, `linkingTotal_neg_direction`, `linkingTotal_smul_direction` |
//! | invariance under an arbitrary admissible projection change | `LinkingIsProjectionInvariant` — an **open** `Prop`, stated and not proved |
//! | [`projected_writhe`] | `projectedWrithe`, `projectedWrithe_neg_direction` |
//! | the projected writhe is direction-dependent | `projectedWrithe_is_not_projection_invariant` — the finite exact counterexample — beside the Rust test `the_projected_writhe_is_not_projection_invariant`, which computes the same `1` against `0` from an explicit polygon |
//!
//! Every theorem named there elaborates with `#print axioms` returning
//! `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::EventId;
use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::exact_value::ExactInterval;
use crate::physical_constraint_complex::{
    ConstraintComponentId, ConstraintEdge, ConstraintError, ConstraintVertexId, ContactClass,
    CoordinateBox3, PhysicalConstraintComplex,
};
use crate::rebase_invariants::{PivotRule, RebaseInvariants, rebase_invariants_on};
use crate::rigidity_receiver::{ExactConfiguration, RigidityError};

// ==============================================================================================
// 1. the aperture filtration
// ==============================================================================================

/// The componentwise maximum of two exact entry intervals.
///
/// For independent interval values this is exactly the range of their maximum, so a simplex's
/// entry value is an exact enclosure and never a chosen representative.
fn interval_max(left: &ExactInterval, right: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: left.lower.clone().max(right.lower.clone()),
        upper: left.upper.clone().max(right.upper.clone()),
    }
}

/// How two exact entry values compare.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ValueOrder {
    /// `left.upper < right.lower`.
    StrictlyBefore,
    /// `right.upper < left.lower`.
    StrictlyAfter,
    /// The two intervals are the same interval: one filtration level holding both cells.
    ExactTie,
    /// They overlap without coinciding. **Not decided, and not tie-broken.**
    Open,
}

/// The exact comparison of two entry values. The only comparison this module makes.
pub fn compare_values(left: &ExactInterval, right: &ExactInterval) -> ValueOrder {
    if left.upper < right.lower {
        ValueOrder::StrictlyBefore
    } else if right.upper < left.lower {
        ValueOrder::StrictlyAfter
    } else if left.lower == right.lower && left.upper == right.upper {
        ValueOrder::ExactTie
    } else {
        ValueOrder::Open
    }
}

/// Two cells whose entry intervals overlap without coinciding: their filtration order is `Open`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenOrderPair {
    pub left: CausalCellId,
    pub right: CausalCellId,
    pub left_value: ExactInterval,
    pub right_value: ExactInterval,
}

/// **The exact aperture filtration of one presented occurrence population.**
///
/// The cells are the simplices of the Vietoris–Rips complex up to a declared top grade whose
/// entry value does not exceed a declared squared ceiling. The entry value of a 1-cell is the
/// exact squared-distance interval of its endpoints; of a higher simplex, the componentwise
/// maximum over its edges; of a vertex, zero.
/// The schema every filtration this module founds declares.
pub const APERTURE_FILTRATION_SCHEMA: &str = "holonic-engine.aperture-filtration.v1";

/// [implemented-exact] **The wire route is gated.** `Deserialize` goes through
/// [`ApertureFiltrationWire`] and [`TryFrom`], which re-runs the coherence
/// [`ApertureFiltration::found_declared`] enforces: the schema, a nonempty population, a valid
/// graded complex, every simplex label inside the occurrence population and of the grade its cell
/// declares, `cells_by_simplex` and `simplex_by_cell` mutually inverse, an entry value for every
/// cell, the filtration property on every face, a top grade inside `1..=3`, and a nonnegative
/// ceiling. Without that gate a remounted filtration could carry a simplex label outside the
/// occurrence population, and [`contact_loops`] would index a map with it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ApertureFiltrationWire")]
pub struct ApertureFiltration {
    pub schema: String,
    pub lineage: String,
    pub source_event: EventId,
    /// The declared squared aperture ceiling. A candidate simplex whose entry interval has
    /// `lower > ceiling` is not founded at all.
    pub ceiling: Rat,
    /// The declared top grade. `1` gives components, `2` adds cycles, `3` adds cavities.
    pub top_grade: u32,
    /// The occurrence addresses, in block order. A simplex is a sorted list of block indices.
    pub occurrences: Vec<ConstraintVertexId>,
    /// Which presented component each occurrence belongs to, when the presentation declares one.
    pub component_of: BTreeMap<ConstraintVertexId, ConstraintComponentId>,
    pub complex: GradedCausalComplex,
    pub entry: BTreeMap<CausalCellId, ExactInterval>,
    pub cells_by_simplex: BTreeMap<Vec<usize>, CausalCellId>,
    pub simplex_by_cell: BTreeMap<CausalCellId, Vec<usize>>,
    /// Pairs of distinct cells carrying the *same* entry interval. One filtration level, two
    /// cells; the secondary key is a declared receiver coordinate and is named here.
    pub exact_ties: Vec<(CausalCellId, CausalCellId)>,
}

/// The wire of an [`ApertureFiltration`]. Every field is re-checked by the `TryFrom` below; there
/// is no unchecked route.
#[derive(Deserialize)]
pub struct ApertureFiltrationWire {
    schema: String,
    lineage: String,
    source_event: EventId,
    ceiling: Rat,
    top_grade: u32,
    occurrences: Vec<ConstraintVertexId>,
    component_of: BTreeMap<ConstraintVertexId, ConstraintComponentId>,
    complex: GradedCausalComplex,
    entry: BTreeMap<CausalCellId, ExactInterval>,
    cells_by_simplex: BTreeMap<Vec<usize>, CausalCellId>,
    simplex_by_cell: BTreeMap<CausalCellId, Vec<usize>>,
    exact_ties: Vec<(CausalCellId, CausalCellId)>,
}

impl TryFrom<ApertureFiltrationWire> for ApertureFiltration {
    type Error = TopologicalError;

    fn try_from(wire: ApertureFiltrationWire) -> Result<Self, Self::Error> {
        if wire.schema != APERTURE_FILTRATION_SCHEMA {
            return Err(TopologicalError::FiltrationSchemaMismatch {
                declared: wire.schema,
                expected: APERTURE_FILTRATION_SCHEMA,
            });
        }
        let rebuilt = ApertureFiltration::found_declared(DeclaredFiltration {
            lineage: wire.lineage,
            source_event: wire.source_event,
            complex: wire.complex,
            occurrences: wire.occurrences,
            component_of: wire.component_of,
            cells_by_simplex: wire.cells_by_simplex,
            entry: wire.entry,
            ceiling: wire.ceiling,
        })?;
        // The derived fields are recomputed by `found_declared`; a wire that carried different
        // ones was not this filtration.
        if rebuilt.top_grade != wire.top_grade
            || rebuilt.simplex_by_cell != wire.simplex_by_cell
            || rebuilt.exact_ties != wire.exact_ties
        {
            return Err(TopologicalError::RemountedFiltrationDisagrees);
        }
        Ok(rebuilt)
    }
}

/// The operands of [`ApertureFiltration::found_declared`], bundled so the constructor takes one
/// addressed object rather than eight positional arguments.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredFiltration {
    pub lineage: String,
    pub source_event: EventId,
    pub complex: GradedCausalComplex,
    pub occurrences: Vec<ConstraintVertexId>,
    pub component_of: BTreeMap<ConstraintVertexId, ConstraintComponentId>,
    pub cells_by_simplex: BTreeMap<Vec<usize>, CausalCellId>,
    pub entry: BTreeMap<CausalCellId, ExactInterval>,
    pub ceiling: Rat,
}

impl ApertureFiltration {
    /// The filtration of a declared occurrence population.
    ///
    /// `positions` are coordinate boxes, so an interval position is admitted here: the filtration
    /// needs only exact interval comparisons. What an interval position costs is the *order*,
    /// which then carries [`OpenOrderPair`]s.
    ///
    /// # What `cell_bound` bounds, and where it is checked
    ///
    /// [definition] `cell_bound` is the declared ceiling on this construction's work. Every stage
    /// of the construction is work sized by the declaration, so the bound is checked at each of
    /// them **before** that stage's work is done, and nothing is ever materialized ahead of a
    /// check:
    ///
    /// 1. **The occurrences.** Every occurrence is founded as a grade-0 cell, so a population of
    ///    more than `cell_bound` occurrences cannot be founded at all. It is refused with
    ///    [`TopologicalError::FiltrationTooWide`] before a single distance is read.
    /// 2. **The pairwise pass.** Every unordered pair is a *candidate* 1-cell, and the pass reads
    ///    one exact squared-distance interval for each, so the pass is itself work of size
    ///    `count·(count−1)/2`. **The admission rule is exactly that this candidate count, formed
    ///    with checked arithmetic, does not exceed `cell_bound`.** A wider declaration is refused
    ///    with [`TopologicalError::PairPopulationTooWide`] before the pass runs, and a count that
    ///    does not fit a machine integer with [`TopologicalError::PairPopulationOverflows`]. A
    ///    caller who wants the pairwise pass over `n` occurrences declares a bound of at least
    ///    `n(n−1)/2`, because that is the work being asked for.
    /// 3. **Every founded cell.** The founded count is checked as each cell is founded and the
    ///    construction refuses with [`TopologicalError::FiltrationTooWide`] the moment it is
    ///    passed. Cofaces are enumerated **lazily, by clique expansion**: a simplex of the
    ///    Vietoris–Rips complex is exactly a clique of the contact graph, so a candidate is
    ///    extended one vertex at a time from an already-founded face — a simplex can only be
    ///    founded if all of its faces are — and no list of `C(n,k)` subsets is built anywhere.
    ///    The enumeration order is the same lexicographic order the subset enumeration had, so
    ///    the founded population, its cell addresses and every reading below are unchanged.
    pub fn found(
        lineage: impl Into<String>,
        source_event: EventId,
        positions: &BTreeMap<ConstraintVertexId, CoordinateBox3>,
        component_of: &BTreeMap<ConstraintVertexId, ConstraintComponentId>,
        ceiling: Rat,
        top_grade: u32,
        cell_bound: usize,
    ) -> Result<Self, TopologicalError> {
        if positions.is_empty() {
            return Err(TopologicalError::EmptyPopulation);
        }
        if top_grade == 0 || top_grade > 3 {
            return Err(TopologicalError::TopGradeOutsideRange(top_grade));
        }
        if ceiling < Rat::zero() {
            return Err(TopologicalError::NegativeCeiling);
        }
        let occurrences = positions.keys().copied().collect::<Vec<_>>();
        let places = positions.values().cloned().collect::<Vec<_>>();
        let count = occurrences.len();

        // (1) Every occurrence is a founded grade-zero cell, so a population past the bound is
        // refused before any distance is read.
        if count > cell_bound {
            return Err(TopologicalError::FiltrationTooWide {
                founded: count,
                bound: cell_bound,
            });
        }
        // (2) The pairwise pass is work of size `count·(count−1)/2` — one candidate 1-cell each —
        // and it is admitted exactly when that candidate population fits the declared bound.
        let candidate_pairs = count
            .checked_mul(count - 1)
            .map(|product| product / 2)
            .ok_or(TopologicalError::PairPopulationOverflows { occurrences: count })?;
        if candidate_pairs > cell_bound {
            return Err(TopologicalError::PairPopulationTooWide {
                occurrences: count,
                candidates: candidate_pairs,
                bound: cell_bound,
            });
        }

        // Every pair's exact squared-distance interval, once. `CoordinateBox3::squared_distance`
        // is the presented complex's own exact reading; nothing here recomputes a distance in a
        // second vocabulary. `neighbours[left]` holds the higher-addressed occurrences `left` is
        // in contact with, which is the contact graph the clique expansion below walks.
        let mut pair_value: BTreeMap<(usize, usize), ExactInterval> = BTreeMap::new();
        let mut neighbours: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); count];
        for left in 0..count {
            for right in (left + 1)..count {
                let value = places[left].squared_distance(&places[right]);
                if value.lower > ceiling {
                    continue;
                }
                pair_value.insert((left, right), value);
                neighbours[left].insert(right);
            }
        }

        let source_events = BTreeSet::from([source_event]);
        let mut complex = GradedCausalComplex::default();
        let mut entry = BTreeMap::new();
        let mut cells_by_simplex: BTreeMap<Vec<usize>, CausalCellId> = BTreeMap::new();
        let mut simplex_by_cell = BTreeMap::new();
        let mut founded = 0usize;

        let found_one = |complex: &mut GradedCausalComplex,
                             entry: &mut BTreeMap<CausalCellId, ExactInterval>,
                             cells_by_simplex: &mut BTreeMap<Vec<usize>, CausalCellId>,
                             simplex_by_cell: &mut BTreeMap<CausalCellId, Vec<usize>>,
                             founded: &mut usize,
                             simplex: Vec<usize>,
                             value: ExactInterval,
                             boundary: CausalChain|
         -> Result<(), TopologicalError> {
            *founded += 1;
            if *founded > cell_bound {
                return Err(TopologicalError::FiltrationTooWide {
                    founded: *founded,
                    bound: cell_bound,
                });
            }
            let grade = u32::try_from(simplex.len() - 1)
                .map_err(|_| TopologicalError::TopGradeOutsideRange(u32::MAX))?;
            let name = simplex
                .iter()
                .map(|at| at.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let cell = complex.found_cell(
                format!("rips[{name}]"),
                source_events.clone(),
                grade,
                boundary,
            )?;
            entry.insert(cell, value);
            cells_by_simplex.insert(simplex.clone(), cell);
            simplex_by_cell.insert(cell, simplex);
            Ok(())
        };

        for at in 0..count {
            found_one(
                &mut complex,
                &mut entry,
                &mut cells_by_simplex,
                &mut simplex_by_cell,
                &mut founded,
                vec![at],
                ExactInterval::point(Rat::zero()),
                CausalChain::default(),
            )?;
        }

        // Grade one: the contact pairs the pass founded, in the lexicographic order the map's own
        // key order already is. `standing` carries the founded simplices of the grade just
        // founded; it is the seed of the clique expansion and is bounded by `cell_bound` because
        // every member of it is a founded cell.
        let mut standing: Vec<Vec<usize>> = Vec::new();
        for (left, right) in pair_value.keys() {
            let simplex = vec![*left, *right];
            let Some(value) = simplex_entry_value(&simplex, &pair_value) else {
                continue;
            };
            if value.lower > ceiling {
                continue;
            }
            let Some(boundary) = simplex_boundary(&simplex, &cells_by_simplex)? else {
                continue;
            };
            found_one(
                &mut complex,
                &mut entry,
                &mut cells_by_simplex,
                &mut simplex_by_cell,
                &mut founded,
                simplex.clone(),
                value,
                boundary,
            )?;
            standing.push(simplex);
        }

        // Grades two and up, by **clique expansion**. A simplex of the Vietoris–Rips complex is a
        // clique of the contact graph, so a candidate coface is an already-founded simplex
        // extended by one higher-addressed occurrence in contact with all of its members. Nothing
        // enumerates subsets: a sparse contact graph costs its own cofaces and no more, and the
        // founded count is checked inside `found_one` at each candidate, so the declared bound
        // refuses the moment it is passed rather than after a list has been built.
        for _ in 2..=top_grade as usize {
            if standing.is_empty() {
                break;
            }
            let mut next: Vec<Vec<usize>> = Vec::new();
            for simplex in &standing {
                let last = *simplex
                    .last()
                    .expect("a founded simplex names at least one occurrence");
                for candidate in neighbours[last].iter().copied() {
                    if !simplex
                        .iter()
                        .all(|member| *member == last || neighbours[*member].contains(&candidate))
                    {
                        continue;
                    }
                    let mut coface = simplex.clone();
                    coface.push(candidate);
                    let Some(value) = simplex_entry_value(&coface, &pair_value) else {
                        continue;
                    };
                    if value.lower > ceiling {
                        continue;
                    }
                    let Some(boundary) = simplex_boundary(&coface, &cells_by_simplex)? else {
                        continue;
                    };
                    found_one(
                        &mut complex,
                        &mut entry,
                        &mut cells_by_simplex,
                        &mut simplex_by_cell,
                        &mut founded,
                        coface.clone(),
                        value,
                        boundary,
                    )?;
                    next.push(coface);
                }
            }
            standing = next;
        }
        complex.validate()?;

        let mut exact_ties = Vec::new();
        let ordered = entry.iter().collect::<Vec<_>>();
        for (at, (left, left_value)) in ordered.iter().enumerate() {
            for (right, right_value) in ordered.iter().skip(at + 1) {
                if compare_values(left_value, right_value) == ValueOrder::ExactTie {
                    exact_ties.push((**left, **right));
                }
            }
        }

        Ok(Self {
            schema: APERTURE_FILTRATION_SCHEMA.to_owned(),
            lineage: lineage.into(),
            source_event,
            ceiling,
            top_grade,
            occurrences,
            component_of: component_of.clone(),
            complex,
            entry,
            cells_by_simplex,
            simplex_by_cell,
            exact_ties,
        })
    }

    /// The filtration a presented complex already carries.
    ///
    /// Coordinate boxes with width are **admitted** — the filtration is an interval-comparison
    /// question — and the widths surface as [`OpenOrderPair`]s rather than as a silent choice.
    pub fn from_presented(
        complex: &PhysicalConstraintComplex,
        ceiling: Rat,
        top_grade: u32,
        cell_bound: usize,
    ) -> Result<Self, TopologicalError> {
        let positions = complex
            .vertices
            .iter()
            .map(|(id, vertex)| (*id, vertex.position.clone()))
            .collect::<BTreeMap<_, _>>();
        let component_of = complex
            .vertices
            .iter()
            .map(|(id, vertex)| (*id, vertex.component))
            .collect::<BTreeMap<_, _>>();
        Self::found(
            complex.presentation_lineage.clone(),
            complex.source_event,
            &positions,
            &component_of,
            ceiling,
            top_grade,
            cell_bound,
        )
    }

    /// **A filtration over a complex that is not a Rips complex.**
    ///
    /// The aperture filtration above is the physical one. A declared complex reaches the same
    /// readings — persistence over a declared field, and the integral profile beside it — and is
    /// the only way to present a complex carrying torsion, which no Rips complex on rational
    /// points in three dimensions is going to hand over on request.
    ///
    /// Every condition the readings depend on is checked: every cell carries an entry value, the
    /// simplex labels have the size their grade demands, and the entry value of a face never
    /// exceeds the entry value of a cell it bounds — which is what makes every sublevel set a
    /// subcomplex.
    pub fn found_declared(declared: DeclaredFiltration) -> Result<Self, TopologicalError> {
        let DeclaredFiltration {
            lineage,
            source_event,
            complex,
            occurrences,
            component_of,
            cells_by_simplex,
            entry,
            ceiling,
        } = declared;
        complex.validate()?;
        if occurrences.is_empty() {
            return Err(TopologicalError::EmptyPopulation);
        }
        if ceiling < Rat::zero() {
            return Err(TopologicalError::NegativeCeiling);
        }
        let mut occurrence_set = BTreeSet::new();
        for occurrence in &occurrences {
            if !occurrence_set.insert(*occurrence) {
                return Err(TopologicalError::OccurrenceAddressRepeated(*occurrence));
            }
        }
        if component_of.len() != occurrences.len()
            || component_of
                .keys()
                .any(|occurrence| !occurrence_set.contains(occurrence))
        {
            return Err(TopologicalError::ComponentMapDisagrees);
        }
        let mut simplex_by_cell = BTreeMap::new();
        for (simplex, cell) in &cells_by_simplex {
            if simplex.iter().any(|at| *at >= occurrences.len()) {
                return Err(TopologicalError::SimplexLabelDisagrees(*cell));
            }
            let grade = complex.cell(*cell)?.grade;
            if usize::try_from(grade).unwrap_or(usize::MAX) + 1 != simplex.len() {
                return Err(TopologicalError::SimplexLabelDisagrees(*cell));
            }
            simplex_by_cell.insert(*cell, simplex.clone());
        }
        let mut top_grade = 0;
        for (id, cell) in complex.cells() {
            if !entry.contains_key(id) {
                return Err(TopologicalError::CellCarriesNoEntryValue(*id));
            }
            if !simplex_by_cell.contains_key(id) {
                return Err(TopologicalError::SimplexLabelDisagrees(*id));
            }
            top_grade = top_grade.max(cell.grade);
            for face in cell.boundary.support() {
                let face_value = entry
                    .get(&face)
                    .ok_or(TopologicalError::CellCarriesNoEntryValue(face))?;
                let cell_value = &entry[id];
                if face_value.lower > cell_value.lower || face_value.upper > cell_value.upper {
                    return Err(TopologicalError::OrderIsNotAFiltration { cell: *id, face });
                }
            }
        }
        let mut exact_ties = Vec::new();
        let ordered = entry.iter().collect::<Vec<_>>();
        for (at, (left, left_value)) in ordered.iter().enumerate() {
            for (right, right_value) in ordered.iter().skip(at + 1) {
                if compare_values(left_value, right_value) == ValueOrder::ExactTie {
                    exact_ties.push((**left, **right));
                }
            }
        }
        Ok(Self {
            schema: APERTURE_FILTRATION_SCHEMA.to_owned(),
            lineage,
            source_event,
            ceiling,
            top_grade,
            occurrences,
            component_of,
            complex,
            entry,
            cells_by_simplex,
            simplex_by_cell,
            exact_ties,
        })
    }

    pub fn cell_count(&self) -> usize {
        self.entry.len()
    }

    pub fn grade_of(&self, cell: CausalCellId) -> Result<u32, TopologicalError> {
        Ok(self.complex.cell(cell)?.grade)
    }

    pub fn value_of(&self, cell: CausalCellId) -> Result<&ExactInterval, TopologicalError> {
        self.entry
            .get(&cell)
            .ok_or(TopologicalError::CellCarriesNoEntryValue(cell))
    }

    /// Every entry value is a point, so no comparison between two distinct values is `Open`.
    pub fn order_is_determinate(&self) -> bool {
        self.entry.values().all(ExactInterval::is_point)
    }

    /// The occurrence a grade-0 cell reads.
    pub fn occurrence_of(&self, cell: CausalCellId) -> Result<ConstraintVertexId, TopologicalError> {
        let simplex = self
            .simplex_by_cell
            .get(&cell)
            .ok_or(TopologicalError::CellCarriesNoEntryValue(cell))?;
        if simplex.len() != 1 {
            return Err(TopologicalError::NotAVertexCell(cell));
        }
        Ok(self.occurrences[simplex[0]])
    }
}

/// The entry value of a simplex: the componentwise maximum over its edges, or `None` when some
/// edge was never founded.
fn simplex_entry_value(
    simplex: &[usize],
    pair_value: &BTreeMap<(usize, usize), ExactInterval>,
) -> Option<ExactInterval> {
    let mut value: Option<ExactInterval> = None;
    for (at, left) in simplex.iter().enumerate() {
        for right in simplex.iter().skip(at + 1) {
            let edge = pair_value.get(&(*left, *right))?;
            value = Some(match value {
                None => edge.clone(),
                Some(current) => interval_max(&current, edge),
            });
        }
    }
    value
}

/// The alternating boundary of a simplex over its already-founded faces.
///
/// `None` when some face is not founded. Under the clique expansion that founds the cells this
/// cannot happen — every face of a clique is a clique, founded at the grade below — and the case
/// is kept as the refusal-free skip the subset enumeration had rather than as an assertion.
fn simplex_boundary(
    simplex: &[usize],
    cells_by_simplex: &BTreeMap<Vec<usize>, CausalCellId>,
) -> Result<Option<CausalChain>, TopologicalError> {
    let mut boundary = CausalChain::default();
    for removed in 0..simplex.len() {
        let mut face = simplex.to_vec();
        face.remove(removed);
        match cells_by_simplex.get(&face) {
            Some(cell) => boundary.add_term(
                *cell,
                ComparativeMultiplicity::from_hand(if removed % 2 == 0 { 1 } else { -1 }, 1_u8)?,
            ),
            None => return Ok(None),
        }
    }
    Ok(Some(boundary))
}

/// Every `size`-subset of `0..population`, lexicographically.
///
/// **The founding no longer uses this.** [`ApertureFiltration::found`] enumerates cofaces by
/// clique expansion, which is the Vietoris–Rips construction's own cost and which lets the
/// declared cell bound refuse before any list exists. It is retained for the test fixtures that
/// name a small declared complex by naming every one of its simplices.
#[cfg(test)]
fn combinations(population: usize, size: usize) -> Vec<Vec<usize>> {
    fn visit(
        population: usize,
        remaining: usize,
        next: usize,
        prefix: &mut Vec<usize>,
        result: &mut Vec<Vec<usize>>,
    ) {
        if remaining == 0 {
            result.push(prefix.clone());
            return;
        }
        let last_start = population.saturating_sub(remaining);
        for member in next..=last_start {
            prefix.push(member);
            visit(population, remaining - 1, member + 1, prefix, result);
            prefix.pop();
        }
    }
    if size > population {
        return Vec::new();
    }
    let mut result = Vec::new();
    visit(population, size, 0, &mut Vec::with_capacity(size), &mut result);
    result
}

/// **Every pair of cells whose filtration order is `Open`.**
///
/// Empty exactly when the order is decided up to exact ties, which is the case whenever every
/// presented position is a point.
pub fn open_order_pairs(filtration: &ApertureFiltration) -> Vec<OpenOrderPair> {
    let ordered = filtration.entry.iter().collect::<Vec<_>>();
    let mut open = Vec::new();
    for (at, (left, left_value)) in ordered.iter().enumerate() {
        for (right, right_value) in ordered.iter().skip(at + 1) {
            if compare_values(left_value, right_value) == ValueOrder::Open {
                open.push(OpenOrderPair {
                    left: **left,
                    right: **right,
                    left_value: (*left_value).clone(),
                    right_value: (*right_value).clone(),
                });
            }
        }
    }
    open
}

// ==============================================================================================
// 2. the filtration order, as a family over the open comparisons
// ==============================================================================================

/// The law deciding one admissible linear extension of the exact interval order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderLaw {
    /// Ascending lower endpoint, then grade, then address. One bound of the family.
    ByLowerBound,
    /// Ascending upper endpoint, then grade, then address. The other bound.
    ByUpperBound,
    /// A named order. Refused unless it names every cell exactly once, puts every face before
    /// every cell it bounds, and agrees with every *decided* comparison.
    Declared(Vec<CausalCellId>),
}

/// One admissible filtration order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FiltrationOrder {
    pub law: String,
    pub order: Vec<CausalCellId>,
    pub position: BTreeMap<CausalCellId, usize>,
}

impl FiltrationOrder {
    /// The order a declared law produces, with every admissibility condition checked.
    pub fn found(
        filtration: &ApertureFiltration,
        law: &OrderLaw,
    ) -> Result<Self, TopologicalError> {
        let order = match law {
            OrderLaw::ByLowerBound | OrderLaw::ByUpperBound => {
                let by_lower = matches!(law, OrderLaw::ByLowerBound);
                let mut keyed = filtration
                    .entry
                    .iter()
                    .map(|(cell, value)| {
                        let grade = filtration.complex.cell(*cell).map(|body| body.grade)?;
                        let key = if by_lower {
                            value.lower.clone()
                        } else {
                            value.upper.clone()
                        };
                        Ok((key, grade, *cell))
                    })
                    .collect::<Result<Vec<_>, CausalAlgebraicError>>()?;
                keyed.sort_by(|left, right| {
                    left.0
                        .cmp(&right.0)
                        .then(left.1.cmp(&right.1))
                        .then(left.2.cmp(&right.2))
                });
                keyed.into_iter().map(|(_, _, cell)| cell).collect::<Vec<_>>()
            }
            OrderLaw::Declared(declared) => declared.clone(),
        };

        if order.len() != filtration.entry.len() {
            return Err(TopologicalError::OrderPopulationDisagrees {
                declared: order.len(),
                founded: filtration.entry.len(),
            });
        }
        let mut position = BTreeMap::new();
        for (at, cell) in order.iter().enumerate() {
            if !filtration.entry.contains_key(cell) {
                return Err(TopologicalError::OrderNamesUnfoundedCell(*cell));
            }
            if position.insert(*cell, at).is_some() {
                return Err(TopologicalError::OrderNamesCellTwice(*cell));
            }
        }
        // Every face strictly earlier than every cell it bounds. Without this the sublevel sets
        // are not subcomplexes and no homology reading below means anything.
        for (at, cell) in order.iter().enumerate() {
            for face in filtration.complex.cell(*cell)?.boundary.support() {
                let face_at = position[&face];
                if face_at >= at {
                    return Err(TopologicalError::OrderIsNotAFiltration {
                        cell: *cell,
                        face,
                    });
                }
            }
        }
        // Every decided comparison respected. An `Open` comparison is exactly the one this
        // condition does not constrain, which is what makes the order a family.
        for (at, cell) in order.iter().enumerate() {
            for later in order.iter().skip(at + 1) {
                let left = filtration.value_of(*cell)?;
                let right = filtration.value_of(*later)?;
                if compare_values(left, right) == ValueOrder::StrictlyAfter {
                    return Err(TopologicalError::OrderContradictsExactValues {
                        earlier: *cell,
                        later: *later,
                    });
                }
            }
        }
        let law_name = match law {
            OrderLaw::ByLowerBound => "by-lower-bound",
            OrderLaw::ByUpperBound => "by-upper-bound",
            OrderLaw::Declared(_) => "declared",
        };
        Ok(Self {
            law: law_name.to_owned(),
            order,
            position,
        })
    }

    pub fn support_before(&self, cut: usize) -> BTreeSet<CausalCellId> {
        self.order.iter().take(cut).copied().collect()
    }
}

// ==============================================================================================
// 3. exact fields for the reduction
// ==============================================================================================

/// The coefficient field the persistence reduction runs over.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Coefficients {
    /// Exact rationals.
    Rational,
    /// `𝔽_p` for a declared prime. Compositeness is refused by name.
    PrimeField(BigUint),
}

impl Coefficients {
    pub fn lineage(&self) -> String {
        match self {
            Self::Rational => "Q".to_owned(),
            Self::PrimeField(p) => format!("F_{p}"),
        }
    }
}

/// The operations the reduction needs from a field. Two implementations: `ℚ` and `𝔽_p`.
trait ExactFieldOps {
    type Elem: Clone + PartialEq;
    fn zero(&self) -> Self::Elem;
    fn is_zero(&self, value: &Self::Elem) -> bool;
    fn embed(&self, value: &BigInt) -> Self::Elem;
    fn add_assign(&self, target: &mut Self::Elem, addend: &Self::Elem);
    fn multiply(&self, left: &Self::Elem, right: &Self::Elem) -> Self::Elem;
    /// `−left / right`. `right` is never zero at a call site.
    fn negated_ratio(
        &self,
        left: &Self::Elem,
        right: &Self::Elem,
    ) -> Result<Self::Elem, TopologicalError>;
}

struct RationalField;

impl ExactFieldOps for RationalField {
    type Elem = Rat;
    fn zero(&self) -> Rat {
        Rat::zero()
    }
    fn is_zero(&self, value: &Rat) -> bool {
        value.is_zero()
    }
    fn embed(&self, value: &BigInt) -> Rat {
        Rat::from_integer(value.clone())
    }
    fn add_assign(&self, target: &mut Rat, addend: &Rat) {
        *target = &*target + addend;
    }
    fn multiply(&self, left: &Rat, right: &Rat) -> Rat {
        left * right
    }
    fn negated_ratio(&self, left: &Rat, right: &Rat) -> Result<Rat, TopologicalError> {
        if right.is_zero() {
            return Err(TopologicalError::DivisionByZeroInReduction);
        }
        Ok(-(left / right))
    }
}

#[derive(Debug)]
struct PrimeField {
    modulus: BigInt,
}

/// **The bit-length ceiling within which a declared modulus's primality is *decided*.**
///
/// [definition] A caller declares the modulus, so deciding its primality is work sized by an
/// exterior declaration and needs an explicit ceiling. Trial division to `√n` has none — a
/// 128-bit prime costs `2^64` divisions — so it is not what this receiver does.
///
/// Within this ceiling the decision is the **deterministic** Miller–Rabin test over the bases
/// `{2,3,5,7,11,13,17,19,23,29,31,37}`. That base set is a *proof*: no composite below
/// `3.317 × 10^24` is a strong pseudoprime to all twelve (Sorenson–Webster, verified), and
/// `2^64 ≈ 1.845 × 10^19` sits far inside that range. So every modulus of at most 64 bits is
/// decided exactly, in `O(log n)` modular multiplications on machine integers, and **nothing here
/// is probabilistic**: the bases are fixed, not sampled, and the range is one the base set covers.
///
/// A wider modulus carries no exact decision procedure of bounded work in this module and is
/// refused by name with [`TopologicalError::ModulusExceedsPrimalityCeiling`].
pub const MODULUS_BIT_CEILING: u64 = 64;

/// The twelve bases whose strong-pseudoprime test is a primality *proof* below `3.317 × 10^24`.
const MILLER_RABIN_BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

/// `left · right mod modulus`, through a 128-bit product so nothing wraps.
fn multiply_modulo(left: u64, right: u64, modulus: u64) -> u64 {
    ((u128::from(left) * u128::from(right)) % u128::from(modulus)) as u64
}

/// `base^exponent mod modulus`, by exact square-and-multiply.
fn power_modulo(base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut standing = base % modulus;
    let mut accumulated = 1_u64 % modulus;
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulated = multiply_modulo(accumulated, standing, modulus);
        }
        standing = multiply_modulo(standing, standing, modulus);
        exponent >>= 1;
    }
    accumulated
}

/// **Primality, decided.** Deterministic Miller–Rabin over [`MILLER_RABIN_BASES`], which is exact
/// for every `u64`. No probabilistic acceptance and no early exit on a guess.
pub(crate) fn is_prime(value: u64) -> bool {
    if value < 2 {
        return false;
    }
    for base in MILLER_RABIN_BASES {
        if value == base {
            return true;
        }
        if value.is_multiple_of(base) {
            return false;
        }
    }
    // `value` is odd and larger than every base, so `value − 1 = odd · 2^twos` with `twos ≥ 1`.
    let mut odd = value - 1;
    let mut twos = 0_u32;
    while odd.is_multiple_of(2) {
        odd /= 2;
        twos += 1;
    }
    'base: for base in MILLER_RABIN_BASES {
        let mut standing = power_modulo(base, odd, value);
        if standing == 1 || standing == value - 1 {
            continue;
        }
        for _ in 1..twos {
            standing = multiply_modulo(standing, standing, value);
            if standing == value - 1 {
                continue 'base;
            }
        }
        return false;
    }
    true
}

impl PrimeField {
    /// A declared prime, **decided** within [`MODULUS_BIT_CEILING`] and refused above it.
    ///
    /// The declaration is never trusted: a composite is named with
    /// [`TopologicalError::ModulusIsNotPrime`] and a modulus past the ceiling with
    /// [`TopologicalError::ModulusExceedsPrimalityCeiling`], both before any reduction runs.
    fn declared(modulus: &BigUint) -> Result<Self, TopologicalError> {
        let bits = modulus.bits();
        if bits > MODULUS_BIT_CEILING {
            return Err(TopologicalError::ModulusExceedsPrimalityCeiling {
                bits,
                ceiling: MODULUS_BIT_CEILING,
            });
        }
        let machine = u64::try_from(modulus.clone())
            .map_err(|_| TopologicalError::ModulusIsNotPrime(modulus.clone()))?;
        if !is_prime(machine) {
            return Err(TopologicalError::ModulusIsNotPrime(modulus.clone()));
        }
        Ok(Self {
            modulus: BigInt::from(modulus.clone()),
        })
    }

    fn reduce(&self, value: BigInt) -> BigInt {
        let residue = value % &self.modulus;
        if residue.is_negative() {
            residue + &self.modulus
        } else {
            residue
        }
    }

    /// The modular inverse by the extended Euclidean algorithm. Exact integers only.
    fn inverse(&self, value: &BigInt) -> Result<BigInt, TopologicalError> {
        let (mut old_r, mut r) = (value.clone(), self.modulus.clone());
        let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
        while !r.is_zero() {
            let quotient = &old_r / &r;
            let next_r = &old_r - &quotient * &r;
            old_r = std::mem::replace(&mut r, next_r);
            let next_s = &old_s - &quotient * &s;
            old_s = std::mem::replace(&mut s, next_s);
        }
        if old_r != BigInt::one() && old_r != -BigInt::one() {
            return Err(TopologicalError::DivisionByZeroInReduction);
        }
        if old_r.is_negative() {
            old_s = -old_s;
        }
        Ok(self.reduce(old_s))
    }
}

impl ExactFieldOps for PrimeField {
    type Elem = BigInt;
    fn zero(&self) -> BigInt {
        BigInt::zero()
    }
    fn is_zero(&self, value: &BigInt) -> bool {
        value.is_zero()
    }
    fn embed(&self, value: &BigInt) -> BigInt {
        self.reduce(value.clone())
    }
    fn add_assign(&self, target: &mut BigInt, addend: &BigInt) {
        *target = self.reduce(&*target + addend);
    }
    fn multiply(&self, left: &BigInt, right: &BigInt) -> BigInt {
        self.reduce(left * right)
    }
    fn negated_ratio(&self, left: &BigInt, right: &BigInt) -> Result<BigInt, TopologicalError> {
        if right.is_zero() {
            return Err(TopologicalError::DivisionByZeroInReduction);
        }
        Ok(self.reduce(-(left * self.inverse(right)?)))
    }
}

// ==============================================================================================
// 4. persistence
// ==============================================================================================

/// One birth–death pair, with **exact** values.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PersistencePair {
    /// The homological grade: `0` a component, `1` a cycle, `2` a cavity.
    pub grade: u32,
    pub birth_cell: CausalCellId,
    pub birth_position: usize,
    pub birth_value: ExactInterval,
    /// `None` for an essential class: it is alive at the declared ceiling and this reading does
    /// not claim it ever dies.
    pub death_cell: Option<CausalCellId>,
    pub death_position: Option<usize>,
    pub death_value: Option<ExactInterval>,
}

impl PersistencePair {
    pub fn is_essential(&self) -> bool {
        self.death_cell.is_none()
    }

    /// A pair whose birth and death carry the same exact value: it lives at no aperture at all.
    /// This is a property of the exact values, not of a tolerance.
    pub fn is_exactly_trivial(&self) -> bool {
        match &self.death_value {
            None => false,
            Some(death) => {
                death.lower == self.birth_value.lower && death.upper == self.birth_value.upper
            }
        }
    }

    /// Alive at the sublevel taken after `cut` cells of the order.
    pub fn alive_at(&self, cut: usize) -> bool {
        self.birth_position < cut && self.death_position.is_none_or(|death| death >= cut)
    }
}

/// The complete reading over one declared field and one declared order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PersistenceReading {
    pub schema: String,
    pub lineage: String,
    pub coefficients: Coefficients,
    pub order_law: String,
    /// Every pair, ascending by birth position.
    pub pairs: Vec<PersistencePair>,
    /// Column operations the reduction actually performed. Work, not elapsed time.
    pub column_operations: usize,
    /// The open comparisons this order resolved by choice rather than by exact comparison.
    pub open_order_pairs: usize,
}

impl PersistenceReading {
    pub fn pairs_at_grade(&self, grade: u32) -> Vec<&PersistencePair> {
        self.pairs.iter().filter(|pair| pair.grade == grade).collect()
    }

    /// The Betti number over the declared field at the sublevel taken after `cut` cells.
    pub fn betti_at(&self, grade: u32, cut: usize) -> usize {
        self.pairs
            .iter()
            .filter(|pair| pair.grade == grade && pair.alive_at(cut))
            .count()
    }

    /// The number of classes at `grade` born at or before `birth_cut` and still alive at
    /// `death_cut`: `rank(H_k(K_s) → H_k(K_t))`, the persistent Betti number.
    pub fn persistent_rank(&self, grade: u32, birth_cut: usize, death_cut: usize) -> usize {
        self.pairs
            .iter()
            .filter(|pair| {
                pair.grade == grade
                    && pair.birth_position < birth_cut
                    && pair.death_position.is_none_or(|death| death >= death_cut)
            })
            .count()
    }

    pub fn essential_count(&self, grade: u32) -> usize {
        self.pairs
            .iter()
            .filter(|pair| pair.grade == grade && pair.is_essential())
            .count()
    }
}

/// **The standard reduction, over a declared field — with the grade-zero cross-check enforced.**
///
/// `work_bound` is an explicit ceiling on the number of column additions. The reduction refuses
/// with [`TopologicalError::ReductionTooWide`] rather than running unbounded on hostile input.
///
/// # The two grade-zero routes are required to agree, here
///
/// [implemented-exact] Before the reading is returned, [`grade_zero_agreement`] recomputes the
/// grade-0 reading by the independent elder-rule union–find of [`community_persistence`] and
/// compares the death multiset and the essential count. A disagreement is
/// [`TopologicalError::GradeZeroReadingsDisagree`] or
/// [`TopologicalError::GradeZeroEssentialsDisagree`] and the reading is **not** returned. The
/// cross-check is therefore enforced on the production path and not only in a test, which is what
/// the R5 `SourceAccountability` row of [`crate::receiver_atlas::contract_ledger`] claims.
///
/// [`persistence_with_grade_zero_agreement`] returns the agreement object beside the reading for a
/// caller that wants the communities as well; this function discards it.
pub fn persistence(
    filtration: &ApertureFiltration,
    order: &FiltrationOrder,
    coefficients: &Coefficients,
    work_bound: usize,
) -> Result<PersistenceReading, TopologicalError> {
    persistence_with_grade_zero_agreement(filtration, order, coefficients, work_bound)
        .map(|(reading, _)| reading)
}

/// [`persistence`], returning the enforced grade-zero agreement beside the reading.
pub fn persistence_with_grade_zero_agreement(
    filtration: &ApertureFiltration,
    order: &FiltrationOrder,
    coefficients: &Coefficients,
    work_bound: usize,
) -> Result<(PersistenceReading, GradeZeroAgreement), TopologicalError> {
    let reading = persistence_unchecked(filtration, order, coefficients, work_bound)?;
    let agreement = grade_zero_agreement(filtration, order, &reading)?;
    Ok((reading, agreement))
}

/// The reduction alone. Private: every public route runs the grade-zero cross-check, and
/// [`grade_zero_agreement`] itself must not be able to reach a reading that already ran it.
fn persistence_unchecked(
    filtration: &ApertureFiltration,
    order: &FiltrationOrder,
    coefficients: &Coefficients,
    work_bound: usize,
) -> Result<PersistenceReading, TopologicalError> {
    let open = open_order_pairs(filtration).len();
    let (pairing, operations) = match coefficients {
        Coefficients::Rational => {
            reduce(filtration, order, &RationalField, work_bound)?
        }
        Coefficients::PrimeField(modulus) => {
            reduce(filtration, order, &PrimeField::declared(modulus)?, work_bound)?
        }
    };

    let mut death_of: BTreeMap<usize, usize> = BTreeMap::new();
    for (column, low) in pairing.iter().enumerate() {
        if let Some(row) = low {
            death_of.insert(*row, column);
        }
    }

    let mut pairs = Vec::new();
    for (at, cell) in order.order.iter().enumerate() {
        if pairing[at].is_some() {
            // A destroyer. Its own class is the one it kills, recorded at the birth below.
            continue;
        }
        let grade = filtration.grade_of(*cell)?;
        let birth_value = filtration.value_of(*cell)?.clone();
        match death_of.get(&at) {
            Some(death_at) => {
                let death_cell = order.order[*death_at];
                pairs.push(PersistencePair {
                    grade,
                    birth_cell: *cell,
                    birth_position: at,
                    birth_value,
                    death_cell: Some(death_cell),
                    death_position: Some(*death_at),
                    death_value: Some(filtration.value_of(death_cell)?.clone()),
                });
            }
            None => pairs.push(PersistencePair {
                grade,
                birth_cell: *cell,
                birth_position: at,
                birth_value,
                death_cell: None,
                death_position: None,
                death_value: None,
            }),
        }
    }

    Ok(PersistenceReading {
        schema: "holonic-engine.persistence-reading.v1".to_owned(),
        lineage: filtration.lineage.clone(),
        coefficients: coefficients.clone(),
        order_law: order.law.clone(),
        pairs,
        column_operations: operations,
        open_order_pairs: open,
    })
}

fn reduce<F: ExactFieldOps>(
    filtration: &ApertureFiltration,
    order: &FiltrationOrder,
    field: &F,
    work_bound: usize,
) -> Result<(Vec<Option<usize>>, usize), TopologicalError> {
    let count = order.order.len();
    let mut columns: Vec<BTreeMap<usize, F::Elem>> = Vec::with_capacity(count);
    for cell in &order.order {
        let mut column = BTreeMap::new();
        for (face, coefficient) in filtration.complex.cell(*cell)?.boundary.coefficients() {
            let value = field.embed(&coefficient.difference());
            if field.is_zero(&value) {
                continue;
            }
            column.insert(order.position[face], value);
        }
        columns.push(column);
    }

    let mut low_owner: BTreeMap<usize, usize> = BTreeMap::new();
    let mut pairing = vec![None; count];
    let mut operations = 0usize;
    for at in 0..count {
        loop {
            let Some(low) = columns[at].keys().next_back().copied() else {
                break;
            };
            match low_owner.get(&low).copied() {
                None => {
                    low_owner.insert(low, at);
                    pairing[at] = Some(low);
                    break;
                }
                Some(earlier) => {
                    operations += 1;
                    if operations > work_bound {
                        return Err(TopologicalError::ReductionTooWide {
                            operations,
                            bound: work_bound,
                        });
                    }
                    let factor =
                        field.negated_ratio(&columns[at][&low], &columns[earlier][&low])?;
                    let source = columns[earlier].clone();
                    for (row, value) in &source {
                        let addend = field.multiply(&factor, value);
                        let target = columns[at].entry(*row).or_insert_with(|| field.zero());
                        field.add_assign(target, &addend);
                        if field.is_zero(target) {
                            columns[at].remove(row);
                        }
                    }
                }
            }
        }
    }
    Ok((pairing, operations))
}

// ==============================================================================================
// 5. contact-community persistence
// ==============================================================================================

/// One contact community: a grade-0 class, with the presented components it reaches.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactCommunity {
    pub seed: ConstraintVertexId,
    pub birth: ExactInterval,
    /// The exact squared aperture at which this community merged into an older one. `None` for
    /// the communities still standing at the declared ceiling.
    pub death: Option<ExactInterval>,
    pub members: BTreeSet<ConstraintVertexId>,
    pub components: BTreeSet<ConstraintComponentId>,
}

/// The grade-0 reading with the presented components retained.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunityPersistence {
    pub schema: String,
    pub lineage: String,
    pub communities: Vec<ContactCommunity>,
    /// For each pair of presented components, the **exact** squared aperture at which they first
    /// belong to one community, or `None` when they never do below the declared ceiling.
    pub component_junction: BTreeMap<(ConstraintComponentId, ConstraintComponentId), Option<ExactInterval>>,
    /// The death values of the merged communities, ascending. This multiset is what the matrix
    /// reduction's grade-0 pairs must reproduce.
    pub merge_values: Vec<ExactInterval>,
}

/// **Contact-community persistence by an elder-rule union–find.**
///
/// Every occurrence is born at aperture zero, so every merge kills the community with the later
/// *order* position of its seed — the elder rule, with the declared order as the tie-break that
/// equal births require. The multiset of merge values does not depend on that tie-break and is
/// returned as [`CommunityPersistence::merge_values`] for exactly that reason.
pub fn community_persistence(
    filtration: &ApertureFiltration,
    order: &FiltrationOrder,
) -> Result<CommunityPersistence, TopologicalError> {
    fn root(parent: &mut [usize], mut at: usize) -> usize {
        while parent[at] != at {
            parent[at] = parent[parent[at]];
            at = parent[at];
        }
        at
    }

    let count = filtration.occurrences.len();
    let mut parent = (0..count).collect::<Vec<_>>();
    let mut seed_position = vec![0usize; count];
    for (at, occurrence) in filtration.occurrences.iter().enumerate() {
        let cell = filtration
            .cells_by_simplex
            .get(std::slice::from_ref(&at))
            .ok_or(TopologicalError::OccurrenceCarriesNoCell(*occurrence))?;
        seed_position[at] = order.position[cell];
    }

    let mut death: BTreeMap<usize, ExactInterval> = BTreeMap::new();
    let mut held: BTreeMap<usize, BTreeSet<ConstraintVertexId>> = BTreeMap::new();
    let mut merge_values = Vec::new();
    let mut component_junction: BTreeMap<
        (ConstraintComponentId, ConstraintComponentId),
        Option<ExactInterval>,
    > = BTreeMap::new();
    let mut components = BTreeSet::new();
    for occurrence in &filtration.occurrences {
        if let Some(component) = filtration.component_of.get(occurrence) {
            components.insert(*component);
        }
    }
    let component_list = components.iter().copied().collect::<Vec<_>>();
    for (at, left) in component_list.iter().enumerate() {
        for right in component_list.iter().skip(at + 1) {
            component_junction.insert((*left, *right), None);
        }
    }

    // The member population of every current root, so a junction between two presented components
    // is read the moment it happens rather than reconstructed afterwards.
    let mut members: Vec<BTreeSet<ConstraintVertexId>> = filtration
        .occurrences
        .iter()
        .map(|occurrence| BTreeSet::from([*occurrence]))
        .collect();

    for cell in &order.order {
        let simplex = &filtration.simplex_by_cell[cell];
        if simplex.len() != 2 {
            continue;
        }
        let value = filtration.value_of(*cell)?.clone();
        let left = root(&mut parent, simplex[0]);
        let right = root(&mut parent, simplex[1]);
        if left == right {
            continue;
        }
        let (elder, younger) = if seed_position[left] <= seed_position[right] {
            (left, right)
        } else {
            (right, left)
        };
        death.insert(younger, value.clone());
        merge_values.push(value.clone());
        let joined = std::mem::take(&mut members[younger]);
        for from in &members[elder] {
            for to in &joined {
                let (left_component, right_component) = (
                    filtration.component_of.get(from).copied(),
                    filtration.component_of.get(to).copied(),
                );
                let (Some(first), Some(second)) = (left_component, right_component) else {
                    continue;
                };
                if first == second {
                    continue;
                }
                let key = if first < second {
                    (first, second)
                } else {
                    (second, first)
                };
                if let Some(slot) = component_junction.get_mut(&key)
                    && slot.is_none()
                {
                    *slot = Some(value.clone());
                }
            }
        }
        held.insert(younger, joined.clone());
        members[elder].extend(joined);
        parent[younger] = elder;
    }

    let mut communities = Vec::new();
    for (at, standing) in members.iter().enumerate().take(count) {
        let occurrence = filtration.occurrences[at];
        let community_members = match held.get(&at) {
            Some(snapshot) => snapshot.clone(),
            None => standing.clone(),
        };
        let mut reached = BTreeSet::new();
        for member in &community_members {
            if let Some(component) = filtration.component_of.get(member) {
                reached.insert(*component);
            }
        }
        communities.push(ContactCommunity {
            seed: occurrence,
            birth: ExactInterval::point(Rat::zero()),
            death: death.get(&at).cloned(),
            members: community_members,
            components: reached,
        });
    }
    merge_values.sort_by(|left, right| {
        left.lower
            .cmp(&right.lower)
            .then(left.upper.cmp(&right.upper))
    });

    Ok(CommunityPersistence {
        schema: "holonic-engine.contact-community-persistence.v1".to_owned(),
        lineage: filtration.lineage.clone(),
        communities,
        component_junction,
        merge_values,
    })
}

/// **The grade-zero reading taken twice, and the two computations held to agreement.**
///
/// [definition] The matrix reduction and the elder-rule union–find compute the same object by
/// different routes: the deaths of the grade-0 persistence pairs are the apertures at which two
/// contact communities merge. Nothing makes that true by construction — the reduction never sees
/// a community and the union–find never sees a column — so it is a genuine cross-check, and this
/// is where the library takes it. A disagreement is a **refusal**
/// ([`TopologicalError::GradeZeroReadingsDisagree`] or
/// [`TopologicalError::GradeZeroEssentialsDisagree`]), not a preference for one route.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradeZeroAgreement {
    pub schema: String,
    pub lineage: String,
    /// The death values of the grade-0 persistence pairs, ascending. Equal to
    /// [`CommunityPersistence::merge_values`], because the two computations agreed.
    pub merge_values: Vec<ExactInterval>,
    /// The classes the matrix reduction leaves essential at grade 0, equal to the number of
    /// communities the union–find never merged.
    pub standing: usize,
    pub communities: CommunityPersistence,
}

/// **Where the two grade-zero computations part, exactly.**
///
/// Carried behind a `Box` in [`TopologicalError::GradeZeroReadingsDisagree`] so that naming both
/// exact intervals does not widen every `Result` this module returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradeZeroDisagreement {
    /// How many grade-0 deaths the matrix reduction returned.
    pub matrix: usize,
    /// How many merges the elder-rule union–find returned.
    pub community: usize,
    /// The first ascending position at which the two multisets part.
    pub at: usize,
    pub matrix_value: Option<ExactInterval>,
    pub community_value: Option<ExactInterval>,
}

impl std::fmt::Display for GradeZeroDisagreement {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            out,
            "the two grade-zero computations disagree: the matrix reduction returns {} deaths and \
             the elder-rule union-find {} merges, first parting at position {} with {:?} against \
             {:?}",
            self.matrix, self.community, self.at, self.matrix_value, self.community_value
        )
    }
}

/// **Compute both grade-zero readings and refuse if they part.**
///
/// `reading` must be the persistence of this filtration under this order; a reading taken under a
/// different order law or a different presentation is refused by name rather than compared, since
/// a disagreement would then say nothing.
pub fn grade_zero_agreement(
    filtration: &ApertureFiltration,
    order: &FiltrationOrder,
    reading: &PersistenceReading,
) -> Result<GradeZeroAgreement, TopologicalError> {
    if reading.lineage != filtration.lineage || reading.order_law != order.law {
        return Err(TopologicalError::ReadingIsNotOfThisFiltration {
            reading_lineage: reading.lineage.clone(),
            reading_order: reading.order_law.clone(),
            filtration_lineage: filtration.lineage.clone(),
            order_law: order.law.clone(),
        });
    }
    let communities = community_persistence(filtration, order)?;

    let mut matrix_deaths = reading
        .pairs_at_grade(0)
        .iter()
        .filter_map(|pair| pair.death_value.clone())
        .collect::<Vec<_>>();
    matrix_deaths.sort_by(|left, right| {
        left.lower
            .cmp(&right.lower)
            .then(left.upper.cmp(&right.upper))
    });

    let merges = &communities.merge_values;
    if matrix_deaths != *merges {
        let at = matrix_deaths
            .iter()
            .zip(merges.iter())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| matrix_deaths.len().min(merges.len()));
        return Err(TopologicalError::GradeZeroReadingsDisagree(Box::new(
            GradeZeroDisagreement {
                matrix: matrix_deaths.len(),
                community: merges.len(),
                at,
                matrix_value: matrix_deaths.get(at).cloned(),
                community_value: merges.get(at).cloned(),
            },
        )));
    }

    let essential = reading.essential_count(0);
    let standing = communities
        .communities
        .iter()
        .filter(|community| community.death.is_none())
        .count();
    if essential != standing {
        return Err(TopologicalError::GradeZeroEssentialsDisagree {
            matrix: essential,
            community: standing,
        });
    }

    Ok(GradeZeroAgreement {
        schema: "holonic-engine.grade-zero-agreement.v1".to_owned(),
        lineage: filtration.lineage.clone(),
        merge_values: communities.merge_values.clone(),
        standing,
        communities,
    })
}

// ==============================================================================================
// 6. the integral profile: torsion beside the field reading
// ==============================================================================================

/// The integral invariants of one sublevel complex, as a family over the `Open` cells at that
/// aperture.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TorsionStep {
    /// The declared squared aperture.
    pub aperture: Rat,
    /// Cells whose entry interval straddles the aperture: `Inside` under one resolution and
    /// `Outside` under the other. Never resolved here.
    pub open_cells: Vec<CausalCellId>,
    /// Every `Open` cell refused.
    pub refusing: RebaseInvariants,
    /// Every `Open` cell admitted.
    pub admitting: RebaseInvariants,
}

/// The integral reading across a declared aperture family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TorsionProfile {
    pub schema: String,
    pub lineage: String,
    pub pivot_rule: PivotRule,
    pub steps: Vec<TorsionStep>,
}

impl TorsionProfile {
    /// Every prime dividing a torsion coefficient anywhere in the profile.
    ///
    /// [definition] These are exactly the primes at which the `𝔽_p` Betti numbers must exceed the
    /// `ℚ` Betti numbers somewhere in the filtration. A persistence reading over one field is
    /// blind to them; this is the reading that is not.
    pub fn field_dependence_primes(&self) -> BTreeSet<BigUint> {
        let mut primes = BTreeSet::new();
        for step in &self.steps {
            for invariants in [&step.refusing, &step.admitting] {
                for coefficient in invariants.total_torsion() {
                    let mut remaining = coefficient.magnitude().clone();
                    let mut divisor = BigUint::from(2_u8);
                    while &divisor * &divisor <= remaining {
                        if (&remaining % &divisor).is_zero() {
                            primes.insert(divisor.clone());
                            while (&remaining % &divisor).is_zero() {
                                remaining /= &divisor;
                            }
                        }
                        divisor += BigUint::one();
                    }
                    if remaining > BigUint::one() {
                        primes.insert(remaining);
                    }
                }
            }
        }
        primes
    }

    /// The profile carries no torsion anywhere, so every field returns the same Betti numbers on
    /// every sublevel of the declared family.
    pub fn is_torsion_free(&self) -> bool {
        self.steps.iter().all(|step| {
            step.refusing.total_torsion().is_empty() && step.admitting.total_torsion().is_empty()
        })
    }
}

/// The two supports the aperture trichotomy gives at one squared aperture: `Inside` only, and
/// `Inside ∪ Open`. Both are closed under boundary.
pub fn sublevel_family(
    filtration: &ApertureFiltration,
    aperture: &Rat,
) -> (BTreeSet<CausalCellId>, BTreeSet<CausalCellId>, Vec<CausalCellId>) {
    let mut refusing = BTreeSet::new();
    let mut admitting = BTreeSet::new();
    let mut open = Vec::new();
    for (cell, value) in &filtration.entry {
        match classify_entry(value, aperture) {
            ContactClass::Inside => {
                refusing.insert(*cell);
                admitting.insert(*cell);
            }
            ContactClass::Open => {
                admitting.insert(*cell);
                open.push(*cell);
            }
            ContactClass::Outside => {}
        }
    }
    (refusing, admitting, open)
}

/// The aperture trichotomy, applied to an entry value rather than to a contact reading. This is
/// `physical_constraint_complex::DistanceAperture::classify`'s law, restated on the filtration's
/// own values so that a sublevel set is a family exactly where a contact family is.
pub fn classify_entry(value: &ExactInterval, aperture: &Rat) -> ContactClass {
    if value.upper <= *aperture {
        ContactClass::Inside
    } else if value.lower > *aperture {
        ContactClass::Outside
    } else {
        ContactClass::Open
    }
}

/// **The integral invariants along a declared aperture family, with torsion.**
///
/// Both members of the `Open` family are read at every aperture, through
/// `rebase_invariants::rebase_invariants_on` and therefore through the existing integer Smith
/// normal form. Nothing here reimplements a reduction.
pub fn integral_profile(
    filtration: &ApertureFiltration,
    apertures: &[Rat],
    rule: PivotRule,
) -> Result<TorsionProfile, TopologicalError> {
    let mut steps = Vec::new();
    for aperture in apertures {
        let (refusing_support, admitting_support, open_cells) = sublevel_family(filtration, aperture);
        for support in [&refusing_support, &admitting_support] {
            if !filtration.complex.is_closed_support(support)? {
                return Err(TopologicalError::SublevelIsNotClosed(aperture.clone()));
            }
        }
        steps.push(TorsionStep {
            aperture: aperture.clone(),
            open_cells,
            refusing: rebase_invariants_on(&filtration.complex, Some(&refusing_support), rule)?,
            admitting: rebase_invariants_on(&filtration.complex, Some(&admitting_support), rule)?,
        });
    }
    Ok(TorsionProfile {
        schema: "holonic-engine.aperture-torsion-profile.v1".to_owned(),
        lineage: filtration.lineage.clone(),
        pivot_rule: rule,
        steps,
    })
}

// ==============================================================================================
// 7. curves, projections, crossings
// ==============================================================================================

fn subtract3(left: &[Rat; 3], right: &[Rat; 3]) -> [Rat; 3] {
    [
        &left[0] - &right[0],
        &left[1] - &right[1],
        &left[2] - &right[2],
    ]
}

fn dot3(left: &[Rat; 3], right: &[Rat; 3]) -> Rat {
    &left[0] * &right[0] + &left[1] * &right[1] + &left[2] * &right[2]
}

fn cross3(left: &[Rat; 3], right: &[Rat; 3]) -> [Rat; 3] {
    [
        &(&left[1] * &right[2]) - &(&left[2] * &right[1]),
        &(&left[2] * &right[0]) - &(&left[0] * &right[2]),
        &(&left[0] * &right[1]) - &(&left[1] * &right[0]),
    ]
}

/// `det[a b c] = ⟨a × b, c⟩`.
fn det3(a: &[Rat; 3], b: &[Rat; 3], c: &[Rat; 3]) -> Rat {
    dot3(&cross3(a, b), c)
}

fn is_zero3(value: &[Rat; 3]) -> bool {
    value.iter().all(Rat::is_zero)
}

fn cross2(left: &(Rat, Rat), right: &(Rat, Rat)) -> Rat {
    &(&left.0 * &right.1) - &(&left.1 * &right.0)
}

fn dot2(left: &(Rat, Rat), right: &(Rat, Rat)) -> Rat {
    &(&left.0 * &right.0) + &(&left.1 * &right.1)
}

/// **A declared rational projection direction, with its rational orthogonal frame.**
///
/// `u = w × e` and `v = w × u` for `e` the first coordinate vector not parallel to `w`. Both are
/// rational and both are orthogonal to `w`, so `x ↦ (⟨u,x⟩, ⟨v,x⟩)` is an exact linear projection
/// with kernel `ℚw`, and `x ↦ ⟨w,x⟩` is an exact height increasing toward the viewer. Nothing is
/// normalized, because a normalization would leave `ℚ`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionDirection {
    pub direction: [Rat; 3],
    frame_u: [Rat; 3],
    frame_v: [Rat; 3],
}

impl ProjectionDirection {
    pub fn declared(direction: [Rat; 3]) -> Result<Self, TopologicalError> {
        if is_zero3(&direction) {
            return Err(TopologicalError::Degenerate(
                ProjectionDegeneracy::ZeroProjectionDirection,
            ));
        }
        let unit = |at: usize| -> [Rat; 3] {
            let mut value = [Rat::zero(), Rat::zero(), Rat::zero()];
            value[at] = Rat::one();
            value
        };
        let mut frame_u = None;
        for at in 0..3 {
            let candidate = cross3(&direction, &unit(at));
            if !is_zero3(&candidate) {
                frame_u = Some(candidate);
                break;
            }
        }
        let frame_u = frame_u.ok_or(TopologicalError::Degenerate(
            ProjectionDegeneracy::ZeroProjectionDirection,
        ))?;
        let frame_v = cross3(&direction, &frame_u);
        Ok(Self {
            direction,
            frame_u,
            frame_v,
        })
    }

    pub fn project(&self, place: &[Rat; 3]) -> (Rat, Rat) {
        (dot3(&self.frame_u, place), dot3(&self.frame_v, place))
    }

    pub fn height(&self, place: &[Rat; 3]) -> Rat {
        dot3(&self.direction, place)
    }

    /// `w ↦ −w`. The classical fact that a diagram viewed from the other side has the same
    /// linking number is a **theorem** of this convention, checked by
    /// `the_linking_number_is_unmoved_by_reversing_the_direction`.
    pub fn reversed(&self) -> Result<Self, TopologicalError> {
        Self::declared([
            -self.direction[0].clone(),
            -self.direction[1].clone(),
            -self.direction[2].clone(),
        ])
    }
}

/// A degeneracy of a declared projection, named rather than perturbed away.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionDegeneracy {
    ZeroProjectionDirection,
    /// A segment projects to a point: it is parallel to the projection direction.
    SegmentParallelToProjection {
        curve: usize,
        segment: usize,
    },
    /// Two projected segments lie on one line and overlap: no transversal crossing exists.
    ProjectedSegmentsCollinear {
        left_curve: usize,
        left_segment: usize,
        right_curve: usize,
        right_segment: usize,
    },
    /// The projected intersection falls on a segment endpoint: the diagram is not generic.
    CrossingAtEndpoint {
        left_curve: usize,
        left_segment: usize,
        right_curve: usize,
        right_segment: usize,
    },
    /// The two strands have equal height where their projections meet: no over and no under.
    EqualHeightAtCrossing {
        left_curve: usize,
        left_segment: usize,
        right_curve: usize,
        right_segment: usize,
    },
    /// A polygon carries a zero-length step.
    ZeroLengthSegment {
        curve: usize,
        segment: usize,
    },
    /// Two curves share a place, so they are not two disjoint curves.
    CurvesTouch {
        left_curve: usize,
        left_vertex: usize,
        right_curve: usize,
        right_vertex: usize,
    },
}

/// A closed polygonal curve with exact rational vertices.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClosedPolygon {
    pub lineage: String,
    pub vertices: Vec<[Rat; 3]>,
}

impl ClosedPolygon {
    pub fn declared(
        lineage: impl Into<String>,
        vertices: Vec<[Rat; 3]>,
    ) -> Result<Self, TopologicalError> {
        let polygon = Self {
            lineage: lineage.into(),
            vertices,
        };
        polygon.validated(0)?;
        Ok(polygon)
    }

    /// At least three vertices, and no zero-length step. `curve` is the index this polygon
    /// carries in the reading that is checking it, so a refusal names the curve.
    pub fn validated(&self, curve: usize) -> Result<(), TopologicalError> {
        if self.vertices.len() < 3 {
            return Err(TopologicalError::PolygonTooShort {
                lineage: self.lineage.clone(),
                vertices: self.vertices.len(),
            });
        }
        for segment in 0..self.vertices.len() {
            if is_zero3(&self.step(segment)) {
                return Err(TopologicalError::Degenerate(
                    ProjectionDegeneracy::ZeroLengthSegment { curve, segment },
                ));
            }
        }
        Ok(())
    }

    pub fn segment_count(&self) -> usize {
        self.vertices.len()
    }

    pub fn start(&self, segment: usize) -> &[Rat; 3] {
        &self.vertices[segment % self.vertices.len()]
    }

    pub fn step(&self, segment: usize) -> [Rat; 3] {
        let count = self.vertices.len();
        subtract3(
            &self.vertices[(segment + 1) % count],
            &self.vertices[segment % count],
        )
    }
}

/// One crossing of a diagram: who is over, who is under, and the sign.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Crossing {
    pub over_curve: usize,
    pub over_segment: usize,
    pub under_curve: usize,
    pub under_segment: usize,
    /// `sgn det[t_over, t_under, w]`: `+1` or `−1`, never zero.
    pub sign: i8,
}

/// Whether two declared segments cross in the declared projection, and with what sign.
///
/// `Ok(None)` is *no crossing*, which is a decided answer. Every undecidable configuration is an
/// `Err` naming the degeneracy.
fn crossing_of(
    direction: &ProjectionDirection,
    left: &ClosedPolygon,
    left_curve: usize,
    left_segment: usize,
    right: &ClosedPolygon,
    right_curve: usize,
    right_segment: usize,
) -> Result<Option<Crossing>, TopologicalError> {
    let left_start = left.start(left_segment).clone();
    let left_step = left.step(left_segment);
    let right_start = right.start(right_segment).clone();
    let right_step = right.step(right_segment);

    let projected_left_step = direction.project(&left_step);
    let projected_right_step = direction.project(&right_step);
    if projected_left_step.0.is_zero() && projected_left_step.1.is_zero() {
        return Err(TopologicalError::Degenerate(
            ProjectionDegeneracy::SegmentParallelToProjection {
                curve: left_curve,
                segment: left_segment,
            },
        ));
    }
    if projected_right_step.0.is_zero() && projected_right_step.1.is_zero() {
        return Err(TopologicalError::Degenerate(
            ProjectionDegeneracy::SegmentParallelToProjection {
                curve: right_curve,
                segment: right_segment,
            },
        ));
    }

    let projected_left_start = direction.project(&left_start);
    let projected_right_start = direction.project(&right_start);
    let offset = (
        &projected_right_start.0 - &projected_left_start.0,
        &projected_right_start.1 - &projected_left_start.1,
    );
    let denominator = cross2(&projected_left_step, &projected_right_step);
    if denominator.is_zero() {
        // Parallel in projection. Three cases, all decided exactly: distinct parallel lines are
        // simply no crossing; one line with disjoint parameter ranges is also no crossing; one
        // line with overlapping ranges admits no transversal crossing at all and is refused.
        if !cross2(&offset, &projected_left_step).is_zero() {
            return Ok(None);
        }
        let norm = dot2(&projected_left_step, &projected_left_step);
        let first = dot2(&offset, &projected_left_step) / &norm;
        let second = &first + &(dot2(&projected_right_step, &projected_left_step) / &norm);
        let (low, high) = if first <= second {
            (first, second)
        } else {
            (second, first)
        };
        if high < Rat::zero() || low > Rat::one() {
            return Ok(None);
        }
        return Err(TopologicalError::Degenerate(
            ProjectionDegeneracy::ProjectedSegmentsCollinear {
                left_curve,
                left_segment,
                right_curve,
                right_segment,
            },
        ));
    }

    let left_parameter = cross2(&offset, &projected_right_step) / &denominator;
    let right_parameter = cross2(&offset, &projected_left_step) / &denominator;
    let zero = Rat::zero();
    let one = Rat::one();
    if left_parameter < zero
        || left_parameter > one
        || right_parameter < zero
        || right_parameter > one
    {
        return Ok(None);
    }
    if left_parameter == zero
        || left_parameter == one
        || right_parameter == zero
        || right_parameter == one
    {
        return Err(TopologicalError::Degenerate(
            ProjectionDegeneracy::CrossingAtEndpoint {
                left_curve,
                left_segment,
                right_curve,
                right_segment,
            },
        ));
    }

    let left_height =
        &direction.height(&left_start) + &(&left_parameter * &direction.height(&left_step));
    let right_height =
        &direction.height(&right_start) + &(&right_parameter * &direction.height(&right_step));
    if left_height == right_height {
        return Err(TopologicalError::Degenerate(
            ProjectionDegeneracy::EqualHeightAtCrossing {
                left_curve,
                left_segment,
                right_curve,
                right_segment,
            },
        ));
    }

    let left_is_over = left_height > right_height;
    let determinant = if left_is_over {
        det3(&left_step, &right_step, &direction.direction)
    } else {
        det3(&right_step, &left_step, &direction.direction)
    };
    if determinant.is_zero() {
        // Unreachable while the projections cross transversally — the projected cross product and
        // this determinant are positive multiples of the same quantity — and refused rather than
        // signed zero if the geometry ever says otherwise.
        return Err(TopologicalError::Degenerate(
            ProjectionDegeneracy::ProjectedSegmentsCollinear {
                left_curve,
                left_segment,
                right_curve,
                right_segment,
            },
        ));
    }
    let sign: i8 = if determinant.is_positive() { 1 } else { -1 };
    Ok(Some(if left_is_over {
        Crossing {
            over_curve: left_curve,
            over_segment: left_segment,
            under_curve: right_curve,
            under_segment: right_segment,
            sign,
        }
    } else {
        Crossing {
            over_curve: right_curve,
            over_segment: right_segment,
            under_curve: left_curve,
            under_segment: left_segment,
            sign,
        }
    }))
}

// ==============================================================================================
// 8. linking and writhe
// ==============================================================================================

/// The linking reading of two closed curves under one declared projection direction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinkingReading {
    pub schema: String,
    pub left_lineage: String,
    pub right_lineage: String,
    pub direction: [Rat; 3],
    pub crossings: Vec<Crossing>,
    /// The signed sum over every crossing between the two curves.
    pub total_signed: i64,
    /// The signed sum over the crossings at which the **first** curve passes over the second.
    pub left_over_right: i64,
    /// The signed sum over the crossings at which the **second** passes over the first.
    pub right_over_left: i64,
    /// The linking number, an exact integer. Equal to both half-sums and to half the total; the
    /// three are checked against each other at every reading.
    pub linking_number: i64,
}

/// **The Gauss linking number, as an exact integer, under a declared rational projection.**
///
/// Every crossing between the two curves is enumerated exactly; a degenerate projection is
/// refused by name and never perturbed. The two half-sums are computed separately and required to
/// agree, which is the classical evenness of the total signed crossing count, checked rather than
/// assumed.
pub fn linking_number(
    left: &ClosedPolygon,
    right: &ClosedPolygon,
    direction: &ProjectionDirection,
) -> Result<LinkingReading, TopologicalError> {
    left.validated(0)?;
    right.validated(1)?;
    for (left_at, left_vertex) in left.vertices.iter().enumerate() {
        for (right_at, right_vertex) in right.vertices.iter().enumerate() {
            if left_vertex == right_vertex {
                return Err(TopologicalError::Degenerate(
                    ProjectionDegeneracy::CurvesTouch {
                        left_curve: 0,
                        left_vertex: left_at,
                        right_curve: 1,
                        right_vertex: right_at,
                    },
                ));
            }
        }
    }

    let mut crossings = Vec::new();
    let mut total: i64 = 0;
    let mut left_over: i64 = 0;
    let mut right_over: i64 = 0;
    for left_segment in 0..left.segment_count() {
        for right_segment in 0..right.segment_count() {
            let Some(crossing) =
                crossing_of(direction, left, 0, left_segment, right, 1, right_segment)?
            else {
                continue;
            };
            total = total
                .checked_add(i64::from(crossing.sign))
                .ok_or(TopologicalError::CrossingCountOverflow)?;
            if crossing.over_curve == 0 {
                left_over = left_over
                    .checked_add(i64::from(crossing.sign))
                    .ok_or(TopologicalError::CrossingCountOverflow)?;
            } else {
                right_over = right_over
                    .checked_add(i64::from(crossing.sign))
                    .ok_or(TopologicalError::CrossingCountOverflow)?;
            }
            crossings.push(crossing);
        }
    }
    if left_over != right_over {
        return Err(TopologicalError::LinkingHalvesDisagree {
            left_over_right: left_over,
            right_over_left: right_over,
        });
    }
    if total != left_over + right_over {
        return Err(TopologicalError::LinkingHalvesDisagree {
            left_over_right: left_over,
            right_over_left: right_over,
        });
    }
    Ok(LinkingReading {
        schema: "holonic-engine.linking-reading.v1".to_owned(),
        left_lineage: left.lineage.clone(),
        right_lineage: right.lineage.clone(),
        direction: direction.direction.clone(),
        crossings,
        total_signed: total,
        left_over_right: left_over,
        right_over_left: right_over,
        linking_number: left_over,
    })
}

/// The linking number under every declared admissible direction, with the invariance question
/// answered on the actual data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinkingAcrossDirections {
    pub readings: Vec<LinkingReading>,
    /// Directions refused as degenerate, with the degeneracy that refused them.
    pub refused: Vec<([Rat; 3], ProjectionDegeneracy)>,
}

impl LinkingAcrossDirections {
    /// Every admitted direction returned the same integer.
    pub fn agree(&self) -> bool {
        match self.readings.first() {
            None => false,
            Some(first) => self
                .readings
                .iter()
                .all(|reading| reading.linking_number == first.linking_number),
        }
    }

    pub fn value(&self) -> Option<i64> {
        self.readings.first().map(|reading| reading.linking_number)
    }
}

/// The linking number of one pair across a declared candidate family of projection directions.
pub fn linking_under_directions(
    left: &ClosedPolygon,
    right: &ClosedPolygon,
    candidates: &[[Rat; 3]],
) -> Result<LinkingAcrossDirections, TopologicalError> {
    let mut readings = Vec::new();
    let mut refused = Vec::new();
    for candidate in candidates {
        let direction = match ProjectionDirection::declared(candidate.clone()) {
            Ok(direction) => direction,
            Err(TopologicalError::Degenerate(degeneracy)) => {
                refused.push((candidate.clone(), degeneracy));
                continue;
            }
            Err(other) => return Err(other),
        };
        match linking_number(left, right, &direction) {
            Ok(reading) => readings.push(reading),
            Err(TopologicalError::Degenerate(degeneracy)) => {
                refused.push((candidate.clone(), degeneracy))
            }
            Err(other) => return Err(other),
        }
    }
    if readings.is_empty() {
        return Err(TopologicalError::NoAdmissibleProjection {
            candidates: candidates.len(),
        });
    }
    Ok(LinkingAcrossDirections { readings, refused })
}

/// The signed self-crossing count of one closed polygon under one declared direction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WritheReading {
    pub schema: String,
    pub lineage: String,
    pub direction: [Rat; 3],
    pub crossings: Vec<Crossing>,
    /// **The projected writhe.** An exact integer *for this direction*. The averaged writhe —
    /// the mean of this count over the sphere of directions — is a real number, is not computed
    /// here, and is not claimed.
    pub projected_writhe: i64,
}

/// **The projected writhe. Not an invariant, and not claimed to be one.**
///
/// Adjacent segments share an endpoint and their projections always meet there; those pairs are
/// excluded, which is the standard convention for a polygonal diagram. Every other endpoint
/// incidence is a genuine degeneracy and is refused.
pub fn projected_writhe(
    curve: &ClosedPolygon,
    direction: &ProjectionDirection,
) -> Result<WritheReading, TopologicalError> {
    curve.validated(0)?;
    let count = curve.segment_count();
    let mut crossings = Vec::new();
    let mut writhe: i64 = 0;
    for left in 0..count {
        for right in (left + 1)..count {
            // Adjacent cyclically: they share a vertex by construction.
            if right == left + 1 || (left == 0 && right + 1 == count) {
                continue;
            }
            let Some(crossing) = crossing_of(direction, curve, 0, left, curve, 0, right)? else {
                continue;
            };
            writhe = writhe
                .checked_add(i64::from(crossing.sign))
                .ok_or(TopologicalError::CrossingCountOverflow)?;
            crossings.push(crossing);
        }
    }
    Ok(WritheReading {
        schema: "holonic-engine.projected-writhe-reading.v1".to_owned(),
        lineage: curve.lineage.clone(),
        direction: direction.direction.clone(),
        crossings,
        projected_writhe: writhe,
    })
}

// ==============================================================================================
// 9. contact loops: backbone segments closed by a contact
// ==============================================================================================

/// A backbone segment closed into a polygon by one contact 1-cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactLoop {
    pub component: ConstraintComponentId,
    pub first: ConstraintVertexId,
    pub last: ConstraintVertexId,
    pub first_ordinal: u32,
    pub last_ordinal: u32,
    pub closing_contact: ConstraintEdge,
    pub closing_squared: ExactInterval,
    pub occurrences: Vec<ConstraintVertexId>,
    pub polygon: ClosedPolygon,
}

impl ContactLoop {
    pub fn shares_occurrence(&self, other: &Self) -> bool {
        self.occurrences
            .iter()
            .any(|occurrence| other.occurrences.contains(occurrence))
    }
}

/// **The loops the presented structure actually carries, at one declared aperture.**
///
/// A 1-cell of the filtration whose exact entry interval reads `Inside` at `aperture`, joining two
/// occurrences of one presented component whose chain positions differ by at least
/// `minimum_span`, closes the intervening backbone steps into a closed polygon. The chain order
/// within a component is the ascending address order, which is the order
/// `PhysicalConstraintComplex::found` assigns along a presented chain.
///
/// [definition] **The contacts here are read from the filtration.** This is the reading available
/// when the caller holds a filtration and no presented complex — the filtration holds every pair
/// with its exact squared-distance interval, so it can answer for a pair of one component.
/// [`presented_contact_loops`] is the reading taken from the presentation's **own**
/// within-component contact family, which
/// [`PhysicalConstraintComplex::found_within_component_contact_family`] now founds; it runs this
/// function as a cross-check and refuses on disagreement rather than preferring either source.
///
/// Returns [`TopologicalError::NoCycle`] when no contact closes anything: a zero here would be a
/// reading of a curve that does not exist.
pub fn contact_loops(
    filtration: &ApertureFiltration,
    configuration: &ExactConfiguration,
    aperture: &Rat,
    minimum_span: usize,
) -> Result<Vec<ContactLoop>, TopologicalError> {
    if configuration.dimension() != 3 {
        return Err(TopologicalError::CurveDimensionDisagrees {
            supplied: configuration.dimension(),
        });
    }
    // The chain of every presented component, in ascending address order.
    let mut chains: BTreeMap<ConstraintComponentId, Vec<usize>> = BTreeMap::new();
    for (at, occurrence) in filtration.occurrences.iter().enumerate() {
        let component = filtration
            .component_of
            .get(occurrence)
            .copied()
            .unwrap_or(ConstraintComponentId(0));
        chains.entry(component).or_default().push(at);
    }
    let mut chain_position: BTreeMap<usize, (ConstraintComponentId, usize)> = BTreeMap::new();
    for (component, chain) in &chains {
        for (position, at) in chain.iter().enumerate() {
            chain_position.insert(*at, (*component, position));
        }
    }

    let mut loops = Vec::new();
    for (simplex, cell) in &filtration.cells_by_simplex {
        if simplex.len() != 2 {
            continue;
        }
        let value = filtration.value_of(*cell)?;
        if classify_entry(value, aperture) != ContactClass::Inside {
            continue;
        }
        // A remounted filtration could carry a simplex naming a position outside the occurrence
        // population; the lookup is a typed refusal, never an index panic.
        let position_of = |at: usize| -> Result<(ConstraintComponentId, usize), TopologicalError> {
            chain_position.get(&at).copied().ok_or(
                TopologicalError::SimplexPositionOutsidePopulation {
                    position: at,
                    population: filtration.occurrences.len(),
                },
            )
        };
        let (left_component, left_position) = position_of(simplex[0])?;
        let (right_component, right_position) = position_of(simplex[1])?;
        if left_component != right_component {
            continue;
        }
        let (low, high) = if left_position <= right_position {
            (left_position, right_position)
        } else {
            (right_position, left_position)
        };
        if high < low + minimum_span {
            continue;
        }
        let chain = chains.get(&left_component).ok_or(
            TopologicalError::SimplexPositionOutsidePopulation {
                position: simplex[0],
                population: filtration.occurrences.len(),
            },
        )?;
        let window = chain.get(low..=high).ok_or(
            TopologicalError::SimplexPositionOutsidePopulation {
                position: high,
                population: chain.len(),
            },
        )?;
        let occurrences = window
            .iter()
            .map(|at| {
                filtration.occurrences.get(*at).copied().ok_or(
                    TopologicalError::SimplexPositionOutsidePopulation {
                        position: *at,
                        population: filtration.occurrences.len(),
                    },
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut vertices = Vec::with_capacity(occurrences.len());
        for occurrence in &occurrences {
            let place = configuration.place(*occurrence)?;
            vertices.push([place[0].clone(), place[1].clone(), place[2].clone()]);
        }
        let first = *occurrences.first().expect("the window is nonempty: low <= high");
        let last = *occurrences.last().expect("the window is nonempty: low <= high");
        let polygon = ClosedPolygon::declared(
            format!(
                "{}:c{}:{}-{}",
                filtration.lineage,
                left_component.0,
                low + 1,
                high + 1
            ),
            vertices,
        )?;
        let (edge, _) = ConstraintEdge::new(first, last)?;
        loops.push(ContactLoop {
            component: left_component,
            first,
            last,
            first_ordinal: u32::try_from(low + 1).unwrap_or(u32::MAX),
            last_ordinal: u32::try_from(high + 1).unwrap_or(u32::MAX),
            closing_contact: edge,
            closing_squared: value.clone(),
            occurrences,
            polygon,
        });
    }
    if loops.is_empty() {
        return Err(TopologicalError::NoCycle {
            lineage: filtration.lineage.clone(),
        });
    }
    Ok(loops)
}

/// **The loops the presentation's own within-component contact family carries**, cross-checked
/// against the filtration reading.
///
/// [definition] The contacts come from
/// [`PhysicalConstraintComplex::within_component_family`] — the owner's family at the declared
/// sequence separation — and each `Inside` reading whose ordinals differ by at least
/// `minimum_span` closes the chain segment between them into a polygon, exactly as
/// [`contact_loops`] does. The presentation is the authority on which pairs are contacts; the
/// filtration is then asked the same question and the two answers are required to agree.
///
/// Both requirements are checked before anything is read, because otherwise the two sources are
/// answering different questions:
///
/// * the filtration's chain for `component` must be the component's own occurrence list, in the
///   same order — otherwise a chain position is not an ordinal
///   ([`TopologicalError::PresentedChainDisagrees`]);
/// * `minimum_span` must be at least the family's declared separation `k`, because the family
///   carries no pair below `k` while the filtration carries them all
///   ([`TopologicalError::SpanBelowDeclaredSeparation`]).
///
/// A pair the family reads `Inside` that the filtration does not, or the reverse, is
/// [`TopologicalError::PresentedLoopsDisagree`] naming the pair. Returns
/// [`TopologicalError::NoCycle`] when no contact closes anything.
pub fn presented_contact_loops(
    complex: &PhysicalConstraintComplex,
    component: ConstraintComponentId,
    minimum_separation: u32,
    filtration: &ApertureFiltration,
    configuration: &ExactConfiguration,
    aperture: &Rat,
    minimum_span: usize,
) -> Result<Vec<ContactLoop>, TopologicalError> {
    let family = complex.within_component_family(component, minimum_separation)?;
    if family.aperture.squared != *aperture {
        return Err(TopologicalError::PresentedApertureDisagrees {
            presented: family.aperture.lineage.clone(),
        });
    }
    if minimum_span < minimum_separation as usize {
        return Err(TopologicalError::SpanBelowDeclaredSeparation {
            span: minimum_span,
            separation: minimum_separation,
        });
    }
    let presented = complex.component(component)?.vertices.clone();
    let chain = filtration
        .occurrences
        .iter()
        .copied()
        .filter(|occurrence| {
            filtration
                .component_of
                .get(occurrence)
                .copied()
                .unwrap_or(ConstraintComponentId(0))
                == component
        })
        .collect::<Vec<_>>();
    if chain != presented {
        return Err(TopologicalError::PresentedChainDisagrees {
            component,
            presented: presented.len(),
            filtered: chain.len(),
        });
    }

    // The presentation's own answer: every `Inside` reading of the within-component family whose
    // ordinals span at least `minimum_span` steps.
    let mut presented_pairs = BTreeSet::new();
    for reading in &family.readings {
        if reading.class != ContactClass::Inside {
            continue;
        }
        let (low, high) = if reading.left_ordinal <= reading.right_ordinal {
            (reading.left_ordinal, reading.right_ordinal)
        } else {
            (reading.right_ordinal, reading.left_ordinal)
        };
        if (high - low) as usize >= minimum_span {
            presented_pairs.insert((low, high));
        }
    }

    // The filtration's answer to the same question, and the disagreement if there is one.
    let filtered = match contact_loops(filtration, configuration, aperture, minimum_span) {
        Ok(found) => found,
        Err(TopologicalError::NoCycle { lineage }) => {
            if presented_pairs.is_empty() {
                return Err(TopologicalError::NoCycle { lineage });
            }
            Vec::new()
        }
        Err(other) => return Err(other),
    };
    let mut filtered_pairs = BTreeSet::new();
    for one in &filtered {
        if one.component != component {
            continue;
        }
        filtered_pairs.insert((one.first_ordinal, one.last_ordinal));
    }
    if let Some(pair) = presented_pairs
        .symmetric_difference(&filtered_pairs)
        .next()
        .copied()
    {
        return Err(TopologicalError::PresentedLoopsDisagree {
            component,
            pair,
            presented: presented_pairs.contains(&pair),
        });
    }
    let loops = filtered
        .into_iter()
        .filter(|one| one.component == component)
        .collect::<Vec<_>>();
    if loops.is_empty() {
        return Err(TopologicalError::NoCycle {
            lineage: filtration.lineage.clone(),
        });
    }
    Ok(loops)
}

/// The entanglement reading of two contact loops: the linking number across a declared family of
/// admissible directions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EntanglementReading {
    pub left_lineage: String,
    pub right_lineage: String,
    pub linking: LinkingAcrossDirections,
    /// Threading: the two loops are linked, so neither can be withdrawn from the other without
    /// passing a strand through a strand.
    pub threaded: bool,
}

/// The entanglement of two vertex-disjoint contact loops.
pub fn loop_entanglement(
    left: &ContactLoop,
    right: &ContactLoop,
    candidates: &[[Rat; 3]],
) -> Result<EntanglementReading, TopologicalError> {
    if left.shares_occurrence(right) {
        return Err(TopologicalError::NoLink {
            reason: "the two loops share an occurrence, so they are not two disjoint curves"
                .to_owned(),
        });
    }
    let linking = linking_under_directions(&left.polygon, &right.polygon, candidates)?;
    let threaded = linking.agree() && linking.value().is_some_and(|value| value != 0);
    Ok(EntanglementReading {
        left_lineage: left.polygon.lineage.clone(),
        right_lineage: right.polygon.lineage.clone(),
        linking,
        threaded,
    })
}

// ==============================================================================================
// 10. the claim discipline
// ==============================================================================================

/// What actually stands, when a knot-like claim is admitted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnotLikeWitness {
    pub lineage: String,
    /// Grade-1 classes alive at the declared aperture, over the declared field.
    pub cycles_at_aperture: usize,
    /// Contact loops the presentation carries.
    pub loops: usize,
    /// Pairs of disjoint loops with a nonzero linking number under every admitted direction.
    pub linked_pairs: Vec<(String, String, i64)>,
}

/// **The gate.** A knot-like reading is returned only where a cycle or a link actually exists.
///
/// The three refusals are typed and name what is missing. None of them is a zero.
pub fn knot_like_reading(
    filtration: &ApertureFiltration,
    reading: &PersistenceReading,
    cut: usize,
    loops: &[ContactLoop],
    candidates: &[[Rat; 3]],
) -> Result<KnotLikeWitness, TopologicalError> {
    let cycles = reading.betti_at(1, cut);
    if loops.is_empty() {
        return Err(TopologicalError::NoCycle {
            lineage: filtration.lineage.clone(),
        });
    }
    let mut linked = Vec::new();
    let mut disjoint_pairs = 0usize;
    for (at, left) in loops.iter().enumerate() {
        for right in loops.iter().skip(at + 1) {
            if left.shares_occurrence(right) {
                continue;
            }
            disjoint_pairs += 1;
            let entanglement = loop_entanglement(left, right, candidates)?;
            if entanglement.threaded {
                linked.push((
                    entanglement.left_lineage,
                    entanglement.right_lineage,
                    entanglement.linking.value().unwrap_or(0),
                ));
            }
        }
    }
    if cycles == 0 && linked.is_empty() {
        if disjoint_pairs == 0 {
            return Err(TopologicalError::NoLink {
                reason: "no two contact loops are vertex-disjoint, so no linking question is posed"
                    .to_owned(),
            });
        }
        return Err(TopologicalError::NoCycle {
            lineage: filtration.lineage.clone(),
        });
    }
    Ok(KnotLikeWitness {
        lineage: filtration.lineage.clone(),
        cycles_at_aperture: cycles,
        loops: loops.len(),
        linked_pairs: linked,
    })
}

/// `rank(H_k(K_s) → H_k(K_t))` read off a persistence reading. The persistent Betti number.
pub fn persistent_rank(
    reading: &PersistenceReading,
    grade: u32,
    birth_cut: usize,
    death_cut: usize,
) -> usize {
    reading.persistent_rank(grade, birth_cut, death_cut)
}

// ==============================================================================================
// refusals
// ==============================================================================================

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TopologicalError {
    /// A remounted filtration declares a schema this module does not own.
    #[error("an aperture filtration declaring schema {declared} is not a {expected}")]
    FiltrationSchemaMismatch {
        /// What the wire declared.
        declared: String,
        /// What this module owns.
        expected: &'static str,
    },
    /// A remounted filtration's derived fields are not the ones its own declaration produces.
    #[error(
        "a remounted filtration's top grade, simplex labelling or exact-tie population is not the \
         one its declaration produces"
    )]
    RemountedFiltrationDisagrees,
    /// A simplex names an occurrence position the filtration does not carry.
    #[error("the simplex position {position} is outside the population of {population} occurrences")]
    SimplexPositionOutsidePopulation {
        /// The position named.
        position: usize,
        /// How many occurrences the filtration carries.
        population: usize,
    },
    #[error("the presented constraint complex refused: {0}")]
    Constraint(#[from] ConstraintError),
    #[error("the graded complex refused: {0}")]
    Algebraic(#[from] CausalAlgebraicError),
    #[error("the configuration refused: {0}")]
    Configuration(#[from] RigidityError),
    #[error("a filtration needs at least one occurrence")]
    EmptyPopulation,
    #[error("the declared occurrence population repeats {0:?}")]
    OccurrenceAddressRepeated(ConstraintVertexId),
    #[error("the component map does not address exactly the declared occurrence population")]
    ComponentMapDisagrees,
    #[error("the declared top grade {0} is outside the range 1..=3 this receiver founds")]
    TopGradeOutsideRange(u32),
    #[error("a squared aperture ceiling is never negative")]
    NegativeCeiling,
    #[error(
        "the filtration founded {founded} cells, past the declared bound {bound}; declare a smaller ceiling, a smaller top grade or a larger bound"
    )]
    FiltrationTooWide { founded: usize, bound: usize },
    #[error(
        "the declared population of {occurrences} occurrences presents {candidates} candidate 1-cells, past the declared cell bound {bound}; the pairwise pass reads one exact interval per candidate, so it is work sized by the declaration and is refused before it runs rather than after"
    )]
    PairPopulationTooWide {
        occurrences: usize,
        candidates: usize,
        bound: usize,
    },
    #[error(
        "the declared population of {occurrences} occurrences overflows the machine integer counting its candidate 1-cells"
    )]
    PairPopulationOverflows { occurrences: usize },
    #[error("cell {0:?} carries no entry value in this filtration")]
    CellCarriesNoEntryValue(CausalCellId),
    #[error("cell {0:?} is not a grade-zero cell, so it reads no occurrence")]
    NotAVertexCell(CausalCellId),
    #[error(
        "cell {0:?} carries no simplex label, or a label whose size disagrees with its grade or names an occurrence outside the declared population"
    )]
    SimplexLabelDisagrees(CausalCellId),
    #[error("occurrence {0:?} carries no founded cell in this filtration")]
    OccurrenceCarriesNoCell(ConstraintVertexId),
    #[error("the declared order names {declared} cells where the filtration founded {founded}")]
    OrderPopulationDisagrees { declared: usize, founded: usize },
    #[error("the declared order names cell {0:?}, which this filtration never founded")]
    OrderNamesUnfoundedCell(CausalCellId),
    #[error("the declared order names cell {0:?} twice")]
    OrderNamesCellTwice(CausalCellId),
    #[error(
        "cell {cell:?} is ordered at or before its own face {face:?}; the sublevel sets of this order are not subcomplexes"
    )]
    OrderIsNotAFiltration {
        cell: CausalCellId,
        face: CausalCellId,
    },
    #[error(
        "the declared order puts {earlier:?} before {later:?}, but their exact entry intervals decide the opposite"
    )]
    OrderContradictsExactValues {
        earlier: CausalCellId,
        later: CausalCellId,
    },
    #[error("the declared modulus {0} is not prime, so the coefficients are not a field")]
    ModulusIsNotPrime(BigUint),
    #[error(
        "the declared modulus carries {bits} bits, past the {ceiling}-bit ceiling within which this receiver *decides* primality; a wider modulus is refused by name rather than trial-divided to its square root or accepted on a probabilistic test"
    )]
    ModulusExceedsPrimalityCeiling { bits: u64, ceiling: u64 },
    #[error("the reduction divided by zero; the declared modulus is not a field")]
    DivisionByZeroInReduction,
    #[error(
        "the reduction performed {operations} column additions, past the declared bound {bound}"
    )]
    ReductionTooWide { operations: usize, bound: usize },
    #[error("the sublevel complex at squared aperture {0} is not closed under boundary")]
    SublevelIsNotClosed(Rat),
    #[error(
        "the persistence reading of {reading_lineage:?} under the {reading_order:?} order is not a reading of {filtration_lineage:?} under the {order_law:?} order, so the two grade-zero computations cannot be compared"
    )]
    ReadingIsNotOfThisFiltration {
        reading_lineage: String,
        reading_order: String,
        filtration_lineage: String,
        order_law: String,
    },
    #[error("{0}")]
    GradeZeroReadingsDisagree(Box<GradeZeroDisagreement>),
    #[error(
        "the two grade-zero computations disagree on what still stands: the matrix reduction leaves {matrix} essential classes and the elder-rule union-find {community} unmerged communities"
    )]
    GradeZeroEssentialsDisagree { matrix: usize, community: usize },
    #[error("the projection is degenerate: {0:?}. It is refused, not perturbed")]
    Degenerate(ProjectionDegeneracy),
    #[error("the polygon {lineage} carries {vertices} vertices; a closed curve needs three")]
    PolygonTooShort { lineage: String, vertices: usize },
    #[error("the signed crossing count overflowed an exact 64-bit integer")]
    CrossingCountOverflow,
    #[error(
        "the first curve passes over the second at signed count {left_over_right} and the second over the first at {right_over_left}; the classical equality of the two half-sums failed, so the diagram is not generic"
    )]
    LinkingHalvesDisagree {
        left_over_right: i64,
        right_over_left: i64,
    },
    #[error("none of the {candidates} declared projection directions is admissible for this pair")]
    NoAdmissibleProjection { candidates: usize },
    #[error("a curve needs three coordinates; the configuration supplies {supplied}")]
    CurveDimensionDisagrees { supplied: usize },
    #[error(
        "no embedding: occurrence {occurrence:?} carries a coordinate box of positive width on axis {axis}, so it is a precision question and not a place. A curve through it does not exist and no linking, writhe or crossing is returned for it"
    )]
    NoEmbedding {
        occurrence: ConstraintVertexId,
        axis: usize,
    },
    #[error(
        "no cycle: the presentation {lineage} carries no contact closing any chain segment, so there is no loop to read. A zero would be a claim about a curve that does not exist"
    )]
    NoCycle { lineage: String },
    #[error("no link: {reason}")]
    NoLink { reason: String },
    #[error(
        "the presented within-component family was classified against aperture {presented:?}, which is not the aperture this reading is taken at; the two sources would be answering different questions"
    )]
    PresentedApertureDisagrees { presented: String },
    #[error(
        "the declared minimum span {span} is below the family's declared sequence separation {separation}; the presentation carries no pair below its separation while the filtration carries them all, so the cross-check would report a disagreement that is a difference of question"
    )]
    SpanBelowDeclaredSeparation { span: usize, separation: u32 },
    #[error(
        "component {component:?} presents {presented} occurrences where the filtration carries {filtered} on that component; a chain position is then not a presented ordinal and the two readings cannot be compared"
    )]
    PresentedChainDisagrees {
        component: ConstraintComponentId,
        presented: usize,
        filtered: usize,
    },
    #[error(
        "the presented within-component family and the aperture filtration disagree about pair {pair:?} of component {component:?} (presented reads it a closing contact: {presented}); neither source is preferred and the reading refuses"
    )]
    PresentedLoopsDisagree {
        component: ConstraintComponentId,
        pair: (u32, u32),
        presented: bool,
    },
}

/// **The embedding, or the typed refusal that there is none.**
///
/// A coordinate box with width is a precision question, not a place, and a curve through it does
/// not exist. `rigidity_receiver::ExactConfiguration::from_presented` already refuses it by name;
/// this restates the refusal in the topological vocabulary, so a caller asking for linking or
/// writhe is told that the *embedding* is missing rather than handed a zero.
pub fn embedding_of(
    positions: &BTreeMap<ConstraintVertexId, CoordinateBox3>,
) -> Result<ExactConfiguration, TopologicalError> {
    let mut places = BTreeMap::new();
    for (occurrence, position) in positions {
        let axes = [&position.x, &position.y, &position.z];
        let mut place = Vec::with_capacity(3);
        for (axis, interval) in axes.into_iter().enumerate() {
            if !interval.is_point() {
                return Err(TopologicalError::NoEmbedding {
                    occurrence: *occurrence,
                    axis,
                });
            }
            place.push(interval.lower.clone());
        }
        places.insert(*occurrence, place);
    }
    Ok(ExactConfiguration::declared(3, places)?)
}

/// The same refusal, taken directly from a presented complex.
pub fn embedding_of_presented(
    complex: &PhysicalConstraintComplex,
) -> Result<ExactConfiguration, TopologicalError> {
    match ExactConfiguration::from_presented(complex) {
        Ok(configuration) => Ok(configuration),
        Err(RigidityError::ConfigurationIsNotAPoint { occurrence, axis }) => {
            Err(TopologicalError::NoEmbedding { occurrence, axis })
        }
        Err(other) => Err(TopologicalError::Configuration(other)),
    }
}

#[cfg(test)]
#[path = "topological_receiver/tests.rs"]
mod tests;
