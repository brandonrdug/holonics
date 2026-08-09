//! The deposited derivation circuit, conducted as an exact population current.
//!
//! [`crate::receiver_current`] is a transport law: a passage has a positive characteristic delay,
//! and at each reached site the complete co-present branch demand meets the site's retained
//! capacity, so the required service rounds **dilate every participating branch together**. Nothing
//! is selected by a score, a ranking, or a lexical preference. It has one caller, in the frozen
//! laboratory, and that caller pins `characteristic_delay: 1` on every edge — so its base delay is
//! uniform and only the dilation is material-dependent. It has never been pointed at a derivation
//! circuit.
//!
//! This module points it at one.
//!
//! ## Why this is the right instrument for the question it is answering
//!
//! `research/records/2026-08-08_FACES_GROW_FROM_COLLOCATION_AND_THE_ATOM_IS_NOT_EMPTY.md` §4(iv)
//! records the reason. An elaboration organ walking *recruitment* concluded that seventeen of
//! eighteen recruited identifiers in `standing/output` are **atoms** — nothing declares them, so
//! their downward closure is empty — and therefore undiscriminable. But an atom recruited by ninety
//! derivations is not the same terrain as one recruited by two, and the difference is available
//! **without a score**, because capacitance dilates a *passage delay* rather than ranking anything.
//! That is the distinction `CLAUDE.md` §13 rule 2 turns on: *a scalar that measures is lawful; a
//! scalar that governs is not.*
//!
//! ## The mapping, and why each role is derived rather than declared
//!
//! ```text
//!   site                     a 0-cell of the circuit: a declaration produced, a symbol recruited,
//!                            or (under a founded statement incidence) a result reached
//!   passage                  a 1-cell, oriented by the sign its founded boundary already carries
//!   branch population        what the law itself accumulates: the exact witness-path population
//!   competing occupancy      branch population x the site's active onward passages -- the law's own
//!   capacity                 the number of onward heads the circuit's coarsest declared receiver
//!                            can tell apart
//! ```
//!
//! **The passage direction is read, not chosen.** `derivation_atlas::found_circuit` founds a
//! recruitment 1-cell with boundary `+derivation, -symbol` and a reach 1-cell with
//! `+derivation, -statement`. A boundary is a difference `head - tail`, so the founded orientation
//! runs **symbol -> derivation** and **statement -> derivation**: current flows from the terrain a
//! proof stood on into the proof that stood on it. [`orient_passages`] reads that off
//! [`crate::algebraic::ComparativeMultiplicity::difference`] and nothing here declares it;
//! `the_passage_orientation_is_read_from_the_founded_boundary_and_agrees_with_the_recruitment_key`
//! holds it against `DerivationCircuit::recruitments`, which is a disjoint frame on the same fact.
//!
//! **The capacity is the site's own distinguishing power.** `receiver_current` defines capacity as
//! *"the exact co-present current population which can be served in one round"* — how many
//! simultaneously-present branches a site can dispatch without queueing. A site dispatches a branch
//! by handing it to one onward passage, and two onward passages are simultaneously servable exactly
//! when the site can **tell their heads apart**. The coarsest receiver this circuit declares is the
//! **result reached**: `derivation_atlas` carries, for every derivation vertex, the statements it
//! proved. So two onward heads collapse when they reach the same set of results, and
//! [`CapacityLaw::DistinguishableResults`] is the count of distinct result-sets among a site's
//! onward heads.
//!
//! That is not an analogy imported from outside. The same deposit's own 2-cell reading found that
//! `carrier_transport`, `carrier_transport_direct` and `carrier_transport_relayed` are *one proof
//! under three names* — three heads a result-receiver cannot separate. The capacity law says such
//! heads queue, and the circuit's own filled squares say they are the same demand.
//!
//! **The competing occupancy and the branch population are not computed here at all.** They are what
//! `receiver_current` accumulates while it conducts, which is the whole reason for calling it rather
//! than evaluating a formula: at a site reached by several passages at one chronology the arriving
//! populations **superpose**, and the site's dilation is then driven by an accumulated occupancy that
//! no per-site fan-out count can see. `an_interior_site_dilates_past_its_own_fan_out_on_accumulated_
//! occupancy` is that difference exhibited.
//!
//! ## Which of the five factors `CLAUDE.md` §5 names this mapping supplies
//!
//! §5 records an owed construction, verbatim: *"an exact receiver-local transport law in which
//! capacitance, branch population, source continuity, returned recurrence, and competing current
//! occupancy affect passage delay without turning those relations into a scalar relevance score or
//! deleting the broad routes."*
//!
//! | factor | supplied by |
//! |---|---|
//! | capacitance | [`CapacityLaw`], derived from the circuit's own distinguishing power |
//! | branch population | `receiver_current`'s accumulation; nothing here computes it |
//! | competing current occupancy | `branch_population x active onward passages`, the law's own |
//! | returned recurrence | [`CapacitanceMapping::refound_capacity_on_return`], which re-founds a site's capacity on the co-present population the circuit actually delivered to it, through `set_site_capacity`, without re-founding the site or rewriting prior testimony |
//! | source continuity | [`CharacteristicDelayLaw::SourceContinuity`] — **and this one is supplied by the deposited source, not by the circuit** |
//!
//! The fifth needs its bound stated plainly. `derivation_atlas::Derivation` carries a name, a
//! statement, and a recruitment multiset. It carries **no source coordinate at all** — no file, no
//! line, no position, no order — so the circuit as that module presents it supplies nothing that
//! could serve as source continuity, and a mapping restricted to the circuit must report the term
//! absent. The deposit on disk does carry one: an artifact is a continuous source and its lines are
//! ordered. [`CharacteristicDelayLaw::SourceContinuity`] uses exactly that, and declares exactly
//! what: **the characteristic delay of a passage is one plus the minimal separation, in lines of the
//! deposited source, between the line that founds the head declaration and the nearest line naming
//! the tail identifier, minimized over the artifacts that founded the head.** An identifier named on
//! the theorem line itself conducts in one; one named two lines away in a preamble conducts in three.
//!
//! That term is what the existing caller pins to `1`, and un-pinning it is not cosmetic: a passage's
//! characteristic delay decides *when* a branch arrives, so two branches that superposed under a
//! uniform delay may arrive at different chronologies under source continuity, which changes the
//! co-present population downstream and therefore the service rounds of a site neither passage
//! touches. `source_continuity_changes_a_downstream_co_present_population` exhibits that coupling.
//!
//! **The locating scan is not a second parser.** `read_derivation` decides what a recruitment *is*;
//! [`named_lines`] only asks where in the continuous source an already-established recruitment was
//! witnessed. It applies the two line-level exclusions the atlas applies — a line whose leading word
//! is `end` is skipped, and a `have` line is read only after `:=` — because a location taken on a
//! line the atlas does not read would measure a distance the circuit does not carry.
//!
//! ## Where a reader would have to add a ranking, and why it is not here
//!
//! The return of [`CapacitanceMapping::read`] is a **population**: one row per identifier, carrying
//! its capacity, its co-present population, its service rounds and its passage delays. Beside it
//! [`CapacitanceReading::dilation_classes`] returns the **partition** the dilation induces —
//! service-round count to the set of identifiers with that count. A class is a population and
//! membership is the return.
//!
//! Nothing here sorts identifiers by significance, thresholds them, or truncates to a leading
//! population. The class index is an exact `BigUint` and the classes are presented in the integer's
//! own order, which is the order of the naturals and not an order of importance. **A ranking appears
//! at exactly one step, and that step is outside this module: a reader who reads the class index as
//! a magnitude of importance and takes the largest class has built an inverse-document weight.**
//!
//! The reading actively resists that step, and the resistance is measurable rather than
//! exhortatory: the service-round count is **not monotone** in how often an identifier was recruited.
//! On `standing/output` under the per-route identity, `Soma` is the most-recruited identifier in the
//! entire deposit and lands in a *lower* class than `KernelWitness`, which is recruited less; and
//! `simpa`, recruited by more routes than `contrapose`, lands in a lower class than it does. An
//! ordering that inverts against the count it would be accused of being is not that count.
//!
//! ## The declared controls
//!
//! [`one_result_star`], [`many_result_star`] and [`disjoint_terrain`] are control circuits with
//! predicted dilations, and the predictions are stated before the material is read:
//!
//! - `one_result_star(n)`: the shared symbol faces `n` onward heads that all reach one result, so
//!   the receiver cannot tell them apart, capacity is one, and the prediction is **`n` service
//!   rounds** on the shared symbol against **one** on every private symbol.
//! - `many_result_star(n)`: the same fan-out with `n` distinguishable results, so capacity is `n`
//!   and the prediction is that the dilation is **flat** — one class, exactly one round everywhere.
//! - `disjoint_terrain(n)`: no shared terrain at all, and the prediction is again **flat**. This is
//!   the null control, and a mapping that manufactured spread would fail it.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::LocalSet;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use thiserror::Error;

use crate::algebraic::CausalCellId;
use crate::derivation_atlas::{
    statement_vertex_key, CircuitAperture, Derivation, DerivationCircuit, DerivationIdentity,
};
use crate::receiver_current::{
    ExactReceiverCurrentError, ExactReceiverCurrentLaw, ExactReceiverCurrentPassage,
    ReceiverCurrentPassageId, ReceiverCurrentSiteId,
};

/// How many times the horizon may be doubled before the reading refuses. The horizon is grown
/// until every site the circuit's own reachability says is reachable has returned; a circuit that
/// never satisfies that is a refusal, never a silent truncation.
const HORIZON_DOUBLINGS: u32 = 64;

// ------------------------------------------------------------------ what a site's capacity is

/// What plays the site's retained capacity — *"the exact co-present current population which can be
/// served in one round"*.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CapacityLaw {
    /// The number of distinct **result-sets** among the site's onward heads. Two onward passages
    /// queue against each other exactly when the circuit's coarsest declared receiver — the result
    /// reached — cannot tell their heads apart.
    DistinguishableResults,
    /// The exact number of times the deposit named the identifier.
    ///
    /// **This one is predicted flat at the source layer, by a theorem rather than by a
    /// measurement**, and it is carried here so the prediction can be run rather than asserted.
    /// Every onward head named the identifier at least once, so the occurrence total is never below
    /// the onward fan-out; with a unit branch population the ceiling division is therefore always
    /// one. A receipt that could not have come out otherwise carries no evidence — `CLAUDE.md` §8 —
    /// and this is that receipt, exhibited as one.
    OccurrenceMultiplicity,
}

/// What plays a passage's positive characteristic delay.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CharacteristicDelayLaw {
    /// Every passage carries delay one. This is what the law's one existing caller pins, so it is
    /// the frame every prior use of `receiver_current` was read in.
    Uniform,
    /// One plus the minimal separation, in lines of the deposited source, between the line founding
    /// the head declaration and the nearest line naming the tail identifier.
    SourceContinuity,
}

// ------------------------------------------------------------------ the return

/// One onward passage's delay, as the transport law returned it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageDelayReading {
    pub to: String,
    pub characteristic_delay: u64,
    pub passage_delay: u64,
    pub arrival_chronology: u64,
}

/// One departure of one site: what the complete co-present demand was, and what it cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepartureReading {
    pub departure_chronology: u64,
    pub branch_population: BigUint,
    pub co_present_branch_population: BigUint,
    pub site_capacity: BigUint,
    pub service_rounds: BigUint,
    /// Every onward passage taken at this departure, each with its own delay. Under a uniform
    /// characteristic delay these agree; under source continuity they need not.
    pub passages: Vec<PassageDelayReading>,
}

/// One identifier's complete row. Every identifier the circuit carries has one, whether or not it
/// conducted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiteDelayReading {
    pub identifier: String,
    pub capacity: BigUint,
    /// The site's onward passages in the founded orientation.
    pub onward_passages: usize,
    /// The distinct result-sets among the onward heads — what the capacity counts under
    /// [`CapacityLaw::DistinguishableResults`], carried whole so the capacity is never a bare number.
    pub distinguishable_results: BTreeSet<BTreeSet<String>>,
    /// The chronology at which the current first reached this site, if it did.
    pub arrival_chronology: Option<u64>,
    /// Every departure. Empty for a terminal site and for one the current never reached.
    pub departures: Vec<DepartureReading>,
}

impl SiteDelayReading {
    /// The site has onward passages and the current never reached it.
    pub const fn unreached(&self) -> bool {
        self.arrival_chronology.is_none()
    }

    /// The site conducts nowhere: nothing recruited it onward, so it never departs and its capacity
    /// is inert.
    pub const fn terminal(&self) -> bool {
        self.onward_passages == 0
    }

    /// The service rounds this site's departures required. A site departs at most once per distinct
    /// chronology, so this is one member for every departure.
    pub fn service_rounds(&self) -> Vec<BigUint> {
        self.departures
            .iter()
            .map(|departure| departure.service_rounds.clone())
            .collect()
    }
}

/// The partition the dilation induces. A class is a population; membership is the return.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DilationClasses {
    /// Service-round count to the identifiers whose departure required exactly that many rounds.
    pub by_service_rounds: BTreeMap<BigUint, BTreeSet<String>>,
    /// Identifiers with no onward passage. Their capacity is inert and they have no service round.
    pub terminal: BTreeSet<String>,
    /// Identifiers the current never reached within the grown horizon.
    pub unreached: BTreeSet<String>,
}

impl DilationClasses {
    /// The dilation separates nothing on this material: every departing identifier required the same
    /// number of service rounds.
    ///
    /// This is a first-class return, not a failure. A capacitance reading that cannot separate its
    /// material has measured that the material carries no congestion, and the honest response is to
    /// report it rather than to move the mapping until spread appears.
    pub fn is_vacuous(&self) -> bool {
        self.by_service_rounds.len() <= 1
    }
}

/// One radiation of the circuit, read back as a delay population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapacitanceReading {
    pub capacity_law: CapacityLaw,
    pub delay_law: CharacteristicDelayLaw,
    /// The chronology horizon the reading grew to. Declared, because a horizon is a receiver
    /// coordinate.
    pub horizon: u64,
    /// The sites the current departed from, in the deposit's own name order.
    pub terrain: BTreeSet<String>,
    /// One row per identifier, in name order. The order is lexicographic and carries no claim.
    pub sites: Vec<SiteDelayReading>,
    /// Later arrivals the earliest section could not overwrite: retained testimony, never discarded
    /// failed paths.
    pub deferred: BTreeMap<String, BTreeSet<u64>>,
}

impl CapacitanceReading {
    pub fn site(&self, identifier: &str) -> Option<&SiteDelayReading> {
        self.sites
            .iter()
            .find(|site| site.identifier == identifier)
    }

    pub fn dilation_classes(&self) -> DilationClasses {
        let mut classes = DilationClasses::default();
        for site in &self.sites {
            if site.terminal() {
                classes.terminal.insert(site.identifier.clone());
                continue;
            }
            if site.unreached() {
                classes.unreached.insert(site.identifier.clone());
                continue;
            }
            for rounds in site.service_rounds() {
                classes
                    .by_service_rounds
                    .entry(rounds)
                    .or_default()
                    .insert(site.identifier.clone());
            }
        }
        classes
    }
}

// ------------------------------------------------------------------ refusals

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum DerivationCapacitanceRefusal {
    #[error("the circuit carries no site with an empty incidence: there is no terrain to radiate from")]
    NoTerrain,
    #[error("1-cell {0:?} does not carry an oriented two-ended boundary and is not a passage")]
    UnorientedPassage(CausalCellId),
    #[error("the source population carries {sources} artifacts and the circuit was founded from {derivations}")]
    SourceDoesNotMatchCircuit { sources: usize, derivations: usize },
    #[error("artifact {0} declares a key the circuit does not carry: the aperture key rule has drifted")]
    KeyNotInCircuit(String),
    #[error("identifier {0} is not a site of this circuit")]
    UnknownIdentifier(String),
    #[error("the horizon was doubled {HORIZON_DOUBLINGS} times and {unreturned} reachable sites still did not return")]
    HorizonExhausted { unreturned: usize },
    #[error("{0}")]
    Current(#[from] ExactReceiverCurrentError),
}

// ------------------------------------------------------------------ the orientation, read

/// One passage as the circuit's founded boundary already oriented it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OrientedPassage {
    pub cell: CausalCellId,
    pub tail: String,
    pub head: String,
}

/// Read every 1-cell's direction off the sign its founded boundary carries.
///
/// A boundary is a difference `head - tail`. `derivation_atlas` founds a recruitment with
/// `+derivation, -symbol`, so the founded passage runs symbol -> derivation, and nothing in this
/// module chooses that. A 1-cell whose two ends do not carry opposite hands is not a passage and is
/// refused rather than oriented by a convention.
pub fn orient_passages(
    circuit: &DerivationCircuit,
) -> Result<Vec<OrientedPassage>, DerivationCapacitanceRefusal> {
    let name_of: BTreeMap<CausalCellId, &str> = circuit
        .vertices()
        .iter()
        .map(|(name, id)| (*id, name.as_str()))
        .collect();

    let mut passages = Vec::new();
    for cell in circuit.complex().cells().values() {
        if cell.grade != 1 {
            continue;
        }
        let mut head = None;
        let mut tail = None;
        for (end, coefficient) in cell.boundary.coefficients() {
            let difference = coefficient.difference();
            if difference > num_bigint::BigInt::zero() {
                head = Some(*end);
            } else if difference < num_bigint::BigInt::zero() {
                tail = Some(*end);
            }
        }
        let (Some(head), Some(tail)) = (head, tail) else {
            return Err(DerivationCapacitanceRefusal::UnorientedPassage(cell.id));
        };
        let (Some(head), Some(tail)) = (name_of.get(&head), name_of.get(&tail)) else {
            return Err(DerivationCapacitanceRefusal::UnorientedPassage(cell.id));
        };
        passages.push(OrientedPassage {
            cell: cell.id,
            tail: (*tail).to_owned(),
            head: (*head).to_owned(),
        });
    }
    passages.sort();
    Ok(passages)
}

// ------------------------------------------------------------------ source continuity

/// Every identifier named in one artifact, with the source lines that named it.
///
/// This **locates** an already-established recruitment; it never decides what a recruitment is.
/// The two line-level exclusions the atlas applies are applied here for the same reason it applies
/// them: a location taken on a line the atlas does not read would measure a distance the circuit
/// does not carry.
pub fn named_lines(text: &str) -> BTreeMap<&str, BTreeSet<usize>> {
    let mut located: BTreeMap<&str, BTreeSet<usize>> = BTreeMap::new();
    for (at, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed == "end" || trimmed.starts_with("end ") {
            continue;
        }
        let read = if trimmed == "have" || trimmed.starts_with("have ") {
            match trimmed.split_once(":=") {
                Some((_, right)) => right,
                None => continue,
            }
        } else {
            trimmed
        };
        for token in read.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.')) {
            if token
                .chars()
                .next()
                .is_some_and(|first| first.is_alphabetic() || first == '_')
            {
                located.entry(token).or_default().insert(at);
            }
        }
    }
    located
}

/// The line on which an artifact founds its theorem.
pub fn theorem_line(text: &str) -> Option<usize> {
    text.lines()
        .position(|line| line.trim().starts_with("theorem "))
}

/// The minimal separation, in source lines, between the line founding the theorem and the nearest
/// line naming `identifier`. `None` when the artifact does not name it on a line the atlas reads.
pub fn source_separation(text: &str, identifier: &str) -> Option<u64> {
    let founded = theorem_line(text)?;
    named_lines(text)
        .get(identifier)?
        .iter()
        .map(|at| at.abs_diff(founded) as u64)
        .min()
}

// ------------------------------------------------------------------ the mapping

/// The derivation circuit founded as an exact passage ecology, with the naming that lets a reading
/// be read back in the deposit's own vocabulary.
#[derive(Debug)]
pub struct CapacitanceMapping {
    law: ExactReceiverCurrentLaw,
    aperture: CircuitAperture,
    capacity_law: CapacityLaw,
    delay_law: CharacteristicDelayLaw,
    site_of: BTreeMap<String, ReceiverCurrentSiteId>,
    name_of: BTreeMap<ReceiverCurrentSiteId, String>,
    onward: BTreeMap<String, BTreeSet<String>>,
    distinguishable: BTreeMap<String, BTreeSet<BTreeSet<String>>>,
    terrain: BTreeSet<String>,
    reachable: BTreeSet<String>,
}

impl CapacitanceMapping {
    pub const fn aperture(&self) -> CircuitAperture {
        self.aperture
    }

    pub const fn capacity_law(&self) -> CapacityLaw {
        self.capacity_law
    }

    pub const fn delay_law(&self) -> CharacteristicDelayLaw {
        self.delay_law
    }

    /// The sites nothing founded — every 0-cell with an empty incoming incidence. This is the
    /// circuit's own terrain and it is what the current radiates from.
    pub const fn terrain(&self) -> &BTreeSet<String> {
        &self.terrain
    }

    pub fn capacity(&self, identifier: &str) -> Option<BigUint> {
        let site = self.site_of.get(identifier)?;
        self.law.site(*site).map(|site| site.capacity.clone())
    }

    /// Found the mapping.
    ///
    /// `sources` are the deposited artifact texts in the same order as the `Derivation` population
    /// the circuit was founded from. They are read only under
    /// [`CharacteristicDelayLaw::SourceContinuity`]; pass an empty slice otherwise.
    pub fn found(
        circuit: &DerivationCircuit,
        derivations: &[Derivation],
        sources: &[String],
        capacity_law: CapacityLaw,
        delay_law: CharacteristicDelayLaw,
    ) -> Result<Self, DerivationCapacitanceRefusal> {
        if delay_law == CharacteristicDelayLaw::SourceContinuity
            && sources.len() != derivations.len()
        {
            return Err(DerivationCapacitanceRefusal::SourceDoesNotMatchCircuit {
                sources: sources.len(),
                derivations: derivations.len(),
            });
        }

        let aperture = circuit.aperture();
        let passages = orient_passages(circuit)?;

        let mut onward: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut incoming: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for passage in &passages {
            onward
                .entry(passage.tail.clone())
                .or_default()
                .insert(passage.head.clone());
            incoming
                .entry(passage.head.clone())
                .or_default()
                .insert(passage.tail.clone());
        }

        // What each derivation vertex proved. This is the circuit's own coarsest declared receiver.
        let mut results_of: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
        for (statement, reaching) in circuit.routes() {
            for vertex in reaching {
                results_of
                    .entry(vertex.as_str())
                    .or_default()
                    .insert(statement.clone());
            }
        }

        // The distinct result-sets among each site's onward heads.
        let mut distinguishable: BTreeMap<String, BTreeSet<BTreeSet<String>>> = BTreeMap::new();
        for (tail, heads) in &onward {
            let classes = heads
                .iter()
                .map(|head| {
                    results_of
                        .get(head.as_str())
                        .cloned()
                        .unwrap_or_default()
                })
                .collect();
            distinguishable.insert(tail.clone(), classes);
        }

        // The occurrence total the deposit deposited on each identifier, for the control law.
        let mut occurrences: BTreeMap<&str, u64> = BTreeMap::new();
        for derivation in derivations {
            for (symbol, count) in &derivation.recruited {
                *occurrences.entry(symbol.as_str()).or_default() += u64::from(*count);
            }
        }

        let mut law = ExactReceiverCurrentLaw::new();
        let mut site_of = BTreeMap::new();
        let mut name_of = BTreeMap::new();
        for (name, cell) in circuit.vertices() {
            // A site with no onward passage never departs, so its capacity is inert. The transport
            // law refuses a zero capacity, so an inert capacity is one, and this is declared rather
            // than silently defaulted.
            let capacity = match capacity_law {
                CapacityLaw::DistinguishableResults => distinguishable
                    .get(name)
                    .map_or(0, BTreeSet::len)
                    .max(1),
                CapacityLaw::OccurrenceMultiplicity => occurrences
                    .get(name.as_str())
                    .copied()
                    .unwrap_or(0)
                    .max(1) as usize,
            };
            let id = ReceiverCurrentSiteId(cell.0);
            law.found_site(id, BigUint::from(capacity))?;
            site_of.insert(name.clone(), id);
            name_of.insert(id, name.clone());
        }

        // The source-continuity term: the minimal line separation, over the artifacts founding the
        // head, between the theorem line and the nearest line naming the tail.
        let statement_prefix = statement_vertex_key("");
        let mut separation: BTreeMap<(String, String), u64> = BTreeMap::new();
        if delay_law == CharacteristicDelayLaw::SourceContinuity {
            for (ordinal, (derivation, text)) in derivations.iter().zip(sources).enumerate() {
                let key = match aperture.identity {
                    DerivationIdentity::ByDeclaration => derivation.name.clone(),
                    DerivationIdentity::ByRoute => format!("{}#{ordinal}", derivation.name),
                };
                if !site_of.contains_key(&key) {
                    return Err(DerivationCapacitanceRefusal::KeyNotInCircuit(key));
                }
                let Some(tails) = incoming.get(&key) else {
                    continue;
                };
                for tail in tails {
                    // A statement vertex is witnessed on the theorem line itself: it is what that
                    // line founds, so its separation is zero.
                    let gap = if tail.starts_with(&statement_prefix) {
                        Some(0)
                    } else {
                        source_separation(text, tail)
                    };
                    let Some(gap) = gap else { continue };
                    separation
                        .entry((tail.clone(), key.clone()))
                        .and_modify(|carried| *carried = (*carried).min(gap))
                        .or_insert(gap);
                }
            }
        }

        for passage in &passages {
            let characteristic_delay = match delay_law {
                CharacteristicDelayLaw::Uniform => 1,
                CharacteristicDelayLaw::SourceContinuity => {
                    1 + separation
                        .get(&(passage.tail.clone(), passage.head.clone()))
                        .copied()
                        .unwrap_or(0)
                }
            };
            law.found_passage(ExactReceiverCurrentPassage {
                id: ReceiverCurrentPassageId(passage.cell.0),
                from: site_of[&passage.tail],
                to: site_of[&passage.head],
                characteristic_delay,
            })?;
        }

        let terrain: BTreeSet<String> = circuit
            .vertices()
            .keys()
            .filter(|name| !incoming.contains_key(*name))
            .cloned()
            .collect();
        if terrain.is_empty() {
            return Err(DerivationCapacitanceRefusal::NoTerrain);
        }

        // A second, independent frame on reachability: a plain forward walk over the same passage
        // population, used only to know when the grown horizon has returned everything it can.
        let mut reachable = terrain.clone();
        let mut frontier: Vec<String> = terrain.iter().cloned().collect();
        while let Some(at) = frontier.pop() {
            let Some(heads) = onward.get(&at) else {
                continue;
            };
            for head in heads {
                if reachable.insert(head.clone()) {
                    frontier.push(head.clone());
                }
            }
        }

        Ok(Self {
            law,
            aperture,
            capacity_law,
            delay_law,
            site_of,
            name_of,
            onward,
            distinguishable,
            terrain,
            reachable,
        })
    }

    /// Change one site's retained capacity by returned occurrence.
    ///
    /// This delegates to `receiver_current::set_site_capacity`, which changes the capacity without
    /// changing the site's identity and without rewriting prior passage testimony.
    pub fn set_site_capacity(
        &mut self,
        identifier: &str,
        capacity: BigUint,
    ) -> Result<(), DerivationCapacitanceRefusal> {
        let site = *self
            .site_of
            .get(identifier)
            .ok_or_else(|| DerivationCapacitanceRefusal::UnknownIdentifier(identifier.to_owned()))?;
        self.law.set_site_capacity(site, capacity)?;
        Ok(())
    }

    /// Re-found a site's capacity on what the circuit actually delivered to it.
    ///
    /// **This is the returned-recurrence term.** The founded capacity is a reading of the circuit's
    /// standing; the co-present branch population a radiation *returned* at that site is a reading
    /// of the same site taken by conduct. Re-founding capacity on the return is the receiver
    /// admitting what it received, and it is the one operation in this module that lets a delay move
    /// without any founding changing.
    ///
    /// Returns the capacity that was carried before, and the one now retained. `None` when the site
    /// did not depart in that reading, because there is then nothing returned to found on.
    pub fn refound_capacity_on_return(
        &mut self,
        reading: &CapacitanceReading,
        identifier: &str,
    ) -> Result<Option<(BigUint, BigUint)>, DerivationCapacitanceRefusal> {
        let carried = self
            .capacity(identifier)
            .ok_or_else(|| DerivationCapacitanceRefusal::UnknownIdentifier(identifier.to_owned()))?;
        let Some(site) = reading.site(identifier) else {
            return Err(DerivationCapacitanceRefusal::UnknownIdentifier(
                identifier.to_owned(),
            ));
        };
        let Some(departure) = site.departures.first() else {
            return Ok(None);
        };
        let returned = departure.co_present_branch_population.clone();
        if returned.is_zero() {
            return Ok(None);
        }
        self.set_site_capacity(identifier, returned.clone())?;
        Ok(Some((carried, returned)))
    }

    /// Conduct the circuit and read the delay population back.
    ///
    /// The horizon is **grown**, not chosen: it starts at one passage-delay per site and doubles
    /// until every site the mapping's own forward walk says is reachable has returned. A circuit
    /// that never satisfies that is refused rather than truncated.
    pub fn read(&self) -> Result<CapacitanceReading, DerivationCapacitanceRefusal> {
        let sources: LocalSet<ReceiverCurrentSiteId> =
            self.terrain.iter().map(|name| self.site_of[name]).collect();

        let longest = self
            .law
            .passages()
            .map(|passage| passage.characteristic_delay)
            .max()
            .unwrap_or(1);
        let mut horizon = (self.site_of.len() as u64).saturating_mul(longest).max(1);

        let mut radiation = self.law.radiate_to_horizon(sources.clone(), horizon)?;
        let mut doublings = 0u32;
        while radiation.returned_targets.len() < self.reachable.len() {
            if doublings >= HORIZON_DOUBLINGS {
                return Err(DerivationCapacitanceRefusal::HorizonExhausted {
                    unreturned: self.reachable.len() - radiation.returned_targets.len(),
                });
            }
            horizon = horizon.saturating_mul(2);
            doublings += 1;
            radiation = self.law.radiate_to_horizon(sources.clone(), horizon)?;
        }

        // Group the law's own passage receipts by the site that departed and the chronology it
        // departed at. Nothing is recomputed here; the receipts are the return.
        let mut departures: BTreeMap<&str, BTreeMap<u64, DepartureReading>> = BTreeMap::new();
        for receipt in &radiation.passage_receipts {
            let from = self.name_of[&receipt.from].as_str();
            let to = self.name_of[&receipt.to].clone();
            let slot = departures
                .entry(from)
                .or_default()
                .entry(receipt.departure_chronology)
                .or_insert_with(|| DepartureReading {
                    departure_chronology: receipt.departure_chronology,
                    branch_population: receipt.branch_population.clone(),
                    co_present_branch_population: receipt.co_present_branch_population.clone(),
                    site_capacity: receipt.site_capacity.clone(),
                    service_rounds: receipt.service_rounds.clone(),
                    passages: Vec::new(),
                });
            slot.passages.push(PassageDelayReading {
                to,
                characteristic_delay: receipt.characteristic_delay,
                passage_delay: receipt.passage_delay,
                arrival_chronology: receipt.arrival_chronology,
            });
        }

        let sites = self
            .site_of
            .keys()
            .map(|identifier| {
                let site = self.site_of[identifier];
                SiteDelayReading {
                    identifier: identifier.clone(),
                    capacity: self
                        .law
                        .site(site)
                        .map(|site| site.capacity.clone())
                        .unwrap_or_else(BigUint::one),
                    onward_passages: self.onward.get(identifier).map_or(0, BTreeSet::len),
                    distinguishable_results: self
                        .distinguishable
                        .get(identifier)
                        .cloned()
                        .unwrap_or_default(),
                    arrival_chronology: radiation
                        .arrivals
                        .get(&site)
                        .map(|arrival| arrival.chronology),
                    departures: departures
                        .get(identifier.as_str())
                        .map(|carried| carried.values().cloned().collect())
                        .unwrap_or_default(),
                }
            })
            .collect();

        let mut deferred: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
        for arrival in &radiation.deferred_arrivals {
            deferred
                .entry(self.name_of[&arrival.site].clone())
                .or_default()
                .insert(arrival.chronology);
        }

        Ok(CapacitanceReading {
            capacity_law: self.capacity_law,
            delay_law: self.delay_law,
            horizon,
            terrain: self.terrain.clone(),
            sites,
            deferred,
        })
    }
}

// ------------------------------------------------------------------ the declared control circuits

fn control(name: &str, statement: &str, recruited: &[&str]) -> Derivation {
    Derivation {
        name: name.to_owned(),
        statement: statement.to_owned(),
        recruited: recruited
            .iter()
            .map(|symbol| ((*symbol).to_owned(), 1u32))
            .collect(),
    }
}

/// A declared control: `arms` declarations recruiting one shared symbol and one private symbol
/// each, **all reaching one result**.
///
/// Predicted dilation: the shared symbol faces `arms` onward heads the result-receiver cannot tell
/// apart, so its capacity is one and it requires `arms` service rounds; every private symbol faces
/// one head and requires one.
pub fn one_result_star(arms: usize) -> Vec<Derivation> {
    (0..arms)
        .map(|arm| {
            let private = format!("private{arm}");
            control(
                &format!("arm{arm}"),
                "one result",
                &["sharedTerrain", private.as_str()],
            )
        })
        .collect()
}

/// The same star with **every arm reaching its own result**.
///
/// Predicted dilation: the shared symbol's `arms` onward heads are all distinguishable, so its
/// capacity is `arms` and it requires one service round. The dilation is flat.
pub fn many_result_star(arms: usize) -> Vec<Derivation> {
    (0..arms)
        .map(|arm| {
            let private = format!("private{arm}");
            control(
                &format!("arm{arm}"),
                &format!("result {arm}"),
                &["sharedTerrain", private.as_str()],
            )
        })
        .collect()
}

/// The null control: `arms` declarations with **no shared terrain** and distinct results.
///
/// Predicted dilation: flat. There is nothing to congest, so a mapping that returned spread here
/// would be manufacturing it.
pub fn disjoint_terrain(arms: usize) -> Vec<Derivation> {
    (0..arms)
        .map(|arm| {
            let private = format!("private{arm}");
            control(
                &format!("arm{arm}"),
                &format!("result {arm}"),
                &[private.as_str()],
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_atlas::{found_circuit, read_derivation, RecruitmentCoefficient, StatementIncidence};

    /// `standing/output/lean-proof-production/carrier-transport-00000.lean`, byte for byte. The
    /// preamble is two lines above the theorem line, which is what the source-continuity term
    /// measures.
    const PRODUCTION_ROUTE: &str = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n";

    /// `standing/output/agentic-research-kernel/formal_carry-00003.lean`, byte for byte.
    const RESEARCH_ROUTE: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem formal_carry (h : P) : exactCarrier P := by\n  rw [exact_chart_carry]\n  assumption\nend Soma\n";

    fn circuit_of(derivations: &[Derivation], aperture: CircuitAperture) -> DerivationCircuit {
        found_circuit(derivations, aperture).expect("the aperture is admissible")
    }

    fn read(
        derivations: &[Derivation],
        aperture: CircuitAperture,
        capacity_law: CapacityLaw,
    ) -> CapacitanceReading {
        let circuit = circuit_of(derivations, aperture);
        CapacitanceMapping::found(
            &circuit,
            derivations,
            &[],
            capacity_law,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds a passage ecology")
        .read()
        .expect("the current conducts")
    }

    // ------------------------------------------------------------ the mapping is read, not declared

    #[test]
    fn the_passage_orientation_is_read_from_the_founded_boundary_and_agrees_with_the_recruitment_key(
    ) {
        let derivations = one_result_star(3);
        let circuit = circuit_of(&derivations, CircuitAperture::STATEMENT_INCIDENT);
        let passages = orient_passages(&circuit).expect("every 1-cell is oriented");

        // Every recruitment key `(derivation, symbol)` must appear as a passage symbol -> derivation.
        for (derivation, symbol) in circuit.recruitments().keys() {
            assert!(
                passages
                    .iter()
                    .any(|passage| &passage.tail == symbol && &passage.head == derivation),
                "the founded boundary of {derivation}<-{symbol} does not run symbol -> derivation"
            );
        }
        // And every reach key `(derivation, statement)` as statement -> derivation.
        for (derivation, statement) in circuit.reaches().keys() {
            let vertex = statement_vertex_key(statement);
            assert!(passages
                .iter()
                .any(|passage| passage.tail == vertex && &passage.head == derivation));
        }
        assert_eq!(
            passages.len(),
            circuit.recruitments().len() + circuit.reaches().len()
        );
    }

    #[test]
    fn capacity_counts_the_onward_heads_the_declared_receiver_can_tell_apart() {
        // Two heads proving one result collapse to one class; two heads proving two results do not.
        let one = one_result_star(2);
        let circuit = circuit_of(&one, CircuitAperture::DEPOSITED_READER);
        let mapping = CapacitanceMapping::found(
            &circuit,
            &one,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds");
        assert_eq!(mapping.capacity("sharedTerrain"), Some(BigUint::one()));

        let many = many_result_star(2);
        let circuit = circuit_of(&many, CircuitAperture::DEPOSITED_READER);
        let mapping = CapacitanceMapping::found(
            &circuit,
            &many,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds");
        assert_eq!(mapping.capacity("sharedTerrain"), Some(BigUint::from(2u8)));
    }

    // ------------------------------------------------------------ the declared control predictions

    #[test]
    fn the_one_result_star_dilates_the_shared_terrain_by_exactly_its_fan_out() {
        for arms in [2usize, 3, 5, 9] {
            let derivations = one_result_star(arms);
            let reading = read(
                &derivations,
                CircuitAperture::DEPOSITED_READER,
                CapacityLaw::DistinguishableResults,
            );
            let shared = reading.site("sharedTerrain").expect("the shared terrain is a site");
            assert_eq!(shared.service_rounds(), vec![BigUint::from(arms)]);
            let private = reading.site("private0").expect("a private symbol is a site");
            assert_eq!(private.service_rounds(), vec![BigUint::one()]);

            let classes = reading.dilation_classes();
            assert!(!classes.is_vacuous(), "the prediction is two classes at arms={arms}");
            assert_eq!(
                classes.by_service_rounds.keys().cloned().collect::<Vec<_>>(),
                vec![BigUint::one(), BigUint::from(arms)]
            );
        }
    }

    #[test]
    fn the_many_result_star_is_flat_because_every_onward_head_is_distinguishable() {
        let derivations = many_result_star(5);
        let reading = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        let classes = reading.dilation_classes();
        assert!(classes.is_vacuous());
        assert_eq!(
            classes.by_service_rounds.keys().cloned().collect::<Vec<_>>(),
            vec![BigUint::one()]
        );
    }

    #[test]
    fn the_null_control_with_no_shared_terrain_returns_one_class() {
        let derivations = disjoint_terrain(6);
        let reading = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        let classes = reading.dilation_classes();
        assert!(
            classes.is_vacuous(),
            "a circuit with nothing shared must not dilate: {:?}",
            classes.by_service_rounds
        );
    }

    // ------------------------------------------------------------ the alternative mapping, refuted

    #[test]
    fn the_occurrence_multiplicity_capacity_is_flat_at_the_source_layer_by_theorem() {
        // Every onward head named the identifier at least once, so the occurrence total is never
        // below the onward fan-out and a unit branch population can never require a second round.
        // The prediction is one class, and the star that dilates under the distinguishing capacity
        // is the sharpest place to take it.
        let derivations = one_result_star(9);
        let dilating = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        assert!(!dilating.dilation_classes().is_vacuous());

        let flat = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::OccurrenceMultiplicity,
        );
        assert!(
            flat.dilation_classes().is_vacuous(),
            "the occurrence capacity was predicted flat and returned {:?}",
            flat.dilation_classes().by_service_rounds
        );
    }

    // ------------------------------------------------------------ the law is doing the work

    #[test]
    fn an_interior_site_dilates_past_its_own_fan_out_on_accumulated_occupancy() {
        // A relay: three terrain symbols recruited by one declaration, which is itself recruited by
        // three further declarations proving one result. The relay's own fan-out is three, so a
        // per-site fan-out reading would give it three service rounds; the transport law
        // superposes the three arriving branches first, so the co-present demand is nine.
        let mut derivations = vec![Derivation {
            name: "relay".to_owned(),
            statement: "relayed".to_owned(),
            recruited: [("t0", 1u32), ("t1", 1), ("t2", 1)]
                .into_iter()
                .map(|(symbol, count)| (symbol.to_owned(), count))
                .collect(),
        }];
        for arm in 0..3 {
            derivations.push(control(
                &format!("head{arm}"),
                "one result",
                &["relay"],
            ));
        }
        let reading = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        let relay = reading.site("relay").expect("the relay is a site");
        assert_eq!(relay.onward_passages, 3);
        assert_eq!(relay.capacity, BigUint::one());
        let departure = &relay.departures[0];
        assert_eq!(departure.branch_population, BigUint::from(3u8));
        assert_eq!(
            departure.co_present_branch_population,
            BigUint::from(9u8),
            "the law superposes the three arriving branches before it dilates"
        );
        assert_eq!(departure.service_rounds, BigUint::from(9u8));
    }

    #[test]
    fn a_more_recruited_identifier_can_land_in_a_lower_service_round_class() {
        // `broad` is recruited by four declarations proving four results; `narrow` by three
        // declarations proving one. Broad is recruited more often and dilates less. A reading that
        // inverts against the count it would be accused of being is not that count.
        let mut derivations = Vec::new();
        for arm in 0..4 {
            derivations.push(control(
                &format!("wide{arm}"),
                &format!("result {arm}"),
                &["broad"],
            ));
        }
        for arm in 0..3 {
            derivations.push(control(
                &format!("tight{arm}"),
                "one result",
                &["narrow"],
            ));
        }
        let reading = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        let broad = reading.site("broad").expect("broad is a site");
        let narrow = reading.site("narrow").expect("narrow is a site");
        assert_eq!(broad.onward_passages, 4);
        assert_eq!(narrow.onward_passages, 3);
        assert_eq!(broad.service_rounds(), vec![BigUint::one()]);
        assert_eq!(narrow.service_rounds(), vec![BigUint::from(3u8)]);
    }

    // ------------------------------------------------------------ returned recurrence

    #[test]
    fn returned_occurrence_moves_a_capacity_and_the_downstream_delay_moves_with_it() {
        let derivations = one_result_star(6);
        let circuit = circuit_of(&derivations, CircuitAperture::DEPOSITED_READER);
        let mut mapping = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds");

        let before = mapping.read().expect("the current conducts");
        let carried = before.site("sharedTerrain").expect("a site").clone();
        assert_eq!(carried.capacity, BigUint::one());
        assert_eq!(carried.service_rounds(), vec![BigUint::from(6u8)]);
        let arrival_before = carried.departures[0].passages[0].arrival_chronology;

        let moved = mapping
            .refound_capacity_on_return(&before, "sharedTerrain")
            .expect("the site departed")
            .expect("a returned co-present population was carried");
        assert_eq!(moved, (BigUint::one(), BigUint::from(6u8)));

        let after = mapping.read().expect("the current conducts");
        let now = after.site("sharedTerrain").expect("a site");
        assert_eq!(now.capacity, BigUint::from(6u8));
        assert_eq!(now.service_rounds(), vec![BigUint::one()]);
        assert!(
            now.departures[0].passages[0].arrival_chronology < arrival_before,
            "a capacity that never changes a delay is a constant, not a capacitance"
        );
        // The site kept its identity and the founding was never rebuilt.
        assert_eq!(now.onward_passages, carried.onward_passages);
    }

    // ------------------------------------------------------------ source continuity

    #[test]
    fn source_continuity_reads_the_line_separation_the_deposited_artifact_carries() {
        // `import KernelWitness` is two lines above the theorem line; `namespace Soma` is one;
        // `Prop` and `exactCarrier` are on the theorem line itself; `assumption` is one below.
        assert_eq!(source_separation(PRODUCTION_ROUTE, "KernelWitness"), Some(2));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "Soma"), Some(1));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "Prop"), Some(0));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "exactCarrier"), Some(0));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "assumption"), Some(1));
        // `end Soma` is skipped exactly as the atlas skips it, so the closing line never supplies a
        // nearer location than `namespace Soma` does.
        assert_eq!(source_separation(RESEARCH_ROUTE, "exact_chart_carry"), Some(1));
        assert_eq!(source_separation(RESEARCH_ROUTE, "Soma"), Some(3));
    }

    #[test]
    fn source_continuity_lengthens_the_passage_whose_ends_are_far_apart_in_the_source() {
        let sources = vec![PRODUCTION_ROUTE.to_owned(), RESEARCH_ROUTE.to_owned()];
        let derivations: Vec<Derivation> = sources
            .iter()
            .map(|text| read_derivation(text).expect("a deposited artifact declares a theorem"))
            .collect();
        let circuit = circuit_of(&derivations, CircuitAperture::DEPOSITED_READER);

        let uniform = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds")
        .read()
        .expect("the current conducts");
        let situated = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &sources,
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::SourceContinuity,
        )
        .expect("the circuit founds")
        .read()
        .expect("the current conducts");

        let delay_to = |reading: &CapacitanceReading, from: &str, to: &str| -> u64 {
            reading
                .site(from)
                .expect("a site")
                .departures
                .iter()
                .flat_map(|departure| departure.passages.iter())
                .find(|passage| passage.to == to)
                .expect("the passage was taken")
                .passage_delay
        };

        // On the theorem line: unchanged. Two lines above it: dilated by the separation.
        assert_eq!(delay_to(&uniform, "Prop", "carrier_transport"), 1);
        assert_eq!(delay_to(&situated, "Prop", "carrier_transport"), 1);
        assert_eq!(delay_to(&uniform, "KernelWitness", "carrier_transport"), 1);
        assert_eq!(delay_to(&situated, "KernelWitness", "carrier_transport"), 3);
    }

    #[test]
    fn source_continuity_changes_a_downstream_co_present_population() {
        // The relay is reached by five terrain symbols. Under a uniform delay three of them arrive
        // at one chronology and superpose; source continuity pushes the ones named far from the
        // theorem line to a later arrival, so fewer branches are co-present when the relay departs.
        // Nothing about the relay itself changed: the coupling runs entirely through when its
        // terrain got there.
        let sources = vec![
            "import KernelWitness\nnamespace Soma\ntheorem relay (h : nearTerrain) : someResult := by\n  assumption\nend Soma\n".to_owned(),
            "namespace Soma\ntheorem head0 (h : relay) : done := by\n  assumption\nend Soma\n".to_owned(),
            "namespace Soma\ntheorem head1 (h : relay) : done := by\n  assumption\nend Soma\n".to_owned(),
        ];
        let derivations: Vec<Derivation> = sources
            .iter()
            .map(|text| read_derivation(text).expect("a deposited artifact declares a theorem"))
            .collect();
        let circuit = circuit_of(&derivations, CircuitAperture::DEPOSITED_READER);

        let uniform = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds")
        .read()
        .expect("the current conducts");
        let situated = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &sources,
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::SourceContinuity,
        )
        .expect("the circuit founds")
        .read()
        .expect("the current conducts");

        let relay_uniform = &uniform.site("relay").expect("a site").departures[0];
        let relay_situated = &situated.site("relay").expect("a site").departures[0];
        // `KernelWitness`, `nearTerrain` and `someResult` all reach the relay at chronology one
        // when every passage costs one.
        assert_eq!(relay_uniform.branch_population, BigUint::from(3u8));
        assert_eq!(
            relay_uniform.co_present_branch_population,
            BigUint::from(6u8)
        );
        // `import KernelWitness` sits two lines above the theorem it serves, so under source
        // continuity it no longer arrives with the two identifiers named on the theorem line
        // itself, and the relay's co-present demand drops with it.
        assert_eq!(relay_situated.branch_population, BigUint::from(2u8));
        assert_eq!(
            relay_situated.co_present_branch_population,
            BigUint::from(4u8)
        );
        assert!(relay_situated.service_rounds < relay_uniform.service_rounds);
        // And the branch that no longer superposes is retained rather than lost.
        assert!(situated.deferred.contains_key("relay"));
    }

    // ------------------------------------------------------------ deposited material

    #[test]
    fn two_deposited_atoms_with_empty_recruitment_closures_separate_by_service_rounds() {
        // Neither `assumption` nor `exact_chart_carry` is declared anywhere in this population, so
        // both have an empty downward closure and the elaboration reading cannot separate them.
        // The dilation does.
        let sources = [
            "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n",
            "import KernelWitness\nnamespace Soma\ntheorem carrier_transport_direct (P : Prop) (h : P) : exactCarrier P := by\n  apply exact_chart_carry\n  assumption\nend Soma\n",
            "import KernelWitness\nnamespace Soma\ntheorem carrier_transport_relayed (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n",
            "namespace Soma\ntheorem every_receiver_agrees (a b : Nat) : a = b := rfl\nend Soma\n",
        ];
        let derivations: Vec<Derivation> = sources
            .iter()
            .map(|text| read_derivation(text).expect("a deposited artifact declares a theorem"))
            .collect();
        let reading = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        let assumption = reading.site("assumption").expect("a site");
        let carry = reading.site("exact_chart_carry").expect("a site");
        assert_eq!(assumption.onward_passages, 3);
        assert_eq!(carry.onward_passages, 1);
        assert_ne!(assumption.service_rounds(), carry.service_rounds());
    }

    #[test]
    fn every_identifier_the_circuit_carries_has_a_row_and_a_terminal_site_says_so() {
        let derivations = one_result_star(3);
        let circuit = circuit_of(
            &derivations,
            CircuitAperture {
                identity: DerivationIdentity::ByDeclaration,
                coefficient: RecruitmentCoefficient::Incidence,
                statements: StatementIncidence::Founded,
            },
        );
        let reading = CapacitanceMapping::found(
            &circuit,
            &derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds")
        .read()
        .expect("the current conducts");
        assert_eq!(reading.sites.len(), circuit.vertices().len());
        for site in &reading.sites {
            assert!(!site.unreached(), "{} was never reached", site.identifier);
        }
        // The three declarations are terminal: nothing recruits them onward.
        let classes = reading.dilation_classes();
        assert_eq!(
            classes.terminal,
            ["arm0", "arm1", "arm2"]
                .into_iter()
                .map(str::to_owned)
                .collect::<BTreeSet<_>>()
        );
        assert!(classes.unreached.is_empty());
    }

    #[test]
    fn a_deferred_arrival_is_retained_rather_than_discarded() {
        // The relay reaches `head0` later than the terrain does directly. The late arrival is
        // deferred testimony, not a failed path.
        let mut derivations = vec![Derivation {
            name: "relay".to_owned(),
            statement: "relayed".to_owned(),
            recruited: [("t0", 1u32), ("t1", 1)]
                .into_iter()
                .map(|(symbol, count)| (symbol.to_owned(), count))
                .collect(),
        }];
        derivations.push(control("head0", "one result", &["relay", "t0"]));
        derivations.push(control("head1", "one result", &["relay"]));
        let reading = read(
            &derivations,
            CircuitAperture::DEPOSITED_READER,
            CapacityLaw::DistinguishableResults,
        );
        assert!(
            reading.deferred.contains_key("head0"),
            "the later arrival at head0 must be retained: {:?}",
            reading.deferred
        );
    }
}
