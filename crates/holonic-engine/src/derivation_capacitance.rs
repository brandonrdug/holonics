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
//! ## The horizon is the law's own fixed point, and it used to be a schedule
//!
//! A chronology horizon is a receiver coordinate, so where it comes from is the whole question.
//! Until 2026-08-09 it came from an authored guess and an authored schedule: start at
//! `site_count x longest_characteristic_delay`, **double**, and refuse after sixty-four doublings.
//! Three things were wrong with that and each is checkable.
//!
//! - **The guess is not a bound.** `passage_delay = characteristic_delay + service_rounds - 1` and
//!   `service_rounds` grows with the accumulated branch population, which is multiplicative along
//!   converging routes. A ladder whose branch population doubles per rung arrives far beyond
//!   `site_count x longest`, so the guess undershoots by an unbounded factor and the schedule
//!   silently covers for it.
//! - **The doubling quantized the return.** The reported horizon could only ever be
//!   `guess x 2^k`, so two circuits whose true completion chronologies differ report the same
//!   horizon. The field named as *"declared, because a horizon is a receiver coordinate"* was
//!   reporting the schedule rather than the material.
//! - **The refusal could not fire.** `saturating_mul(2)` from any positive start reaches
//!   `u64::MAX` well inside sixty-four doublings, and at `u64::MAX` every reachable site returns
//!   or the radiation errors on its own carrier extent. `HorizonExhausted` was dead code and the
//!   `64` beside it decided nothing.
//!
//! What replaces it is stated at [`CapacitanceMapping::grow_to_fixed_point`] and carried in
//! [`HorizonFixedPoint`]: the law deposits, as deferred testimony, the exact chronology at which
//! every site it could not return would have arrived, so the growth reads its next horizon off the
//! law instead of inventing one; the growth terminates because each step returns at least one
//! further reachable site, which the circuit's own reachable population bounds; and the horizon
//! finally reported is `max` over the reachable population of the arrival chronology the law
//! returned — **conducted at, and conducted one below, so that being least is measured**.
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
    CircuitAperture, Derivation, DerivationCircuit, DerivationIdentity, statement_vertex_key,
};
use crate::receiver_current::{
    ExactReceiverCurrentError, ExactReceiverCurrentLaw, ExactReceiverCurrentPassage,
    ExactReceiverCurrentRadiation, ReceiverCurrentPassageId, ReceiverCurrentSiteId,
};

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

/// The chronology horizon the reading conducted at, with the two-sided certificate that it is the
/// **transport law's own fixed point** rather than an arithmetic schedule's stopping place.
///
/// A horizon is a receiver coordinate and this is the whole of it. `least_sufficient` is the
/// smallest chronology at which every site the circuit's own forward reachability names has
/// returned; the reading refuses unless coverage is complete there and **strictly incomplete one
/// chronology below**. Both halves are measured by conducting, not asserted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HorizonFixedPoint {
    /// `max` over the reachable population of the arrival chronology the law returned. Below it the
    /// site carrying that maximum is deferred by the law's own `arrival_chronology > horizon` gate,
    /// so no smaller horizon covers the circuit.
    pub least_sufficient: u64,
    /// The circuit's own forward-reachable population — what a sufficient horizon must return.
    pub reachable_sites: usize,
    /// Sites returned at `least_sufficient`. Equal to `reachable_sites`, or the reading refuses.
    pub returned_at_fixed_point: usize,
    /// Sites returned one chronology below it. Strictly fewer, or the reading refuses. `None`
    /// exactly when the fixed point is zero, which is the circuit whose reachable population is its
    /// own terrain and which therefore departs and arrives at one chronology.
    pub returned_one_below: Option<usize>,
    /// Every horizon the growth passed through, in order, starting at zero. **Each entry after the
    /// first is a chronology the transport law itself deposited** as deferred testimony; nothing
    /// here invents one.
    pub grown_through: Vec<u64>,
    /// Sites returned at each entry of `grown_through`, in step. A growth that returned no further
    /// site is a defect and the reading refuses rather than growing again.
    pub returned_at: Vec<usize>,
    /// The growth bound the **material** supplies. Every growth is required to return at least one
    /// further reachable site and the terrain returns at chronology zero, so the reachable
    /// population less one bounds the growths. Exceeding it is a broken theorem, never a budget.
    pub growth_bound: usize,
}

impl HorizonFixedPoint {
    /// Both halves of the certificate: complete at the fixed point, incomplete below it.
    pub fn is_least(&self) -> bool {
        self.returned_at_fixed_point == self.reachable_sites
            && self
                .returned_one_below
                .is_none_or(|below| below < self.reachable_sites)
    }

    /// How many times the horizon was grown before the circuit returned whole.
    pub fn growths(&self) -> usize {
        self.grown_through.len().saturating_sub(1)
    }
}

/// One radiation of the circuit, read back as a delay population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapacitanceReading {
    pub capacity_law: CapacityLaw,
    pub delay_law: CharacteristicDelayLaw,
    /// The chronology horizon the reading conducted at: the transport law's own fixed point, which
    /// is [`HorizonFixedPoint::least_sufficient`] and carries its certificate there.
    pub horizon: u64,
    /// What derives that horizon, and the measurement that it is the least one.
    pub horizon_fixed_point: HorizonFixedPoint,
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
        self.sites.iter().find(|site| site.identifier == identifier)
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

/// **The routes between two named entities, or the named fact that there are none.**
///
/// The two returns are distinct on purpose. `Reached` with an empty `routes` cannot occur — the
/// population and the enumeration are taken from the same arrival body and must agree — so an
/// absence of routes is always `Unreached`, and `Unreached` says which pair did not join rather
/// than handing back a vector the caller has to interpret.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteReading {
    Reached {
        from: String,
        to: String,
        /// The exact number of minimal-arrival routes, taken from the factorized arrival body
        /// **without enumerating them**. It is a `BigUint` because a terrain can carry more routes
        /// than a machine can list, and the count is still exact when the listing is not possible.
        population: BigUint,
        /// The routes, each as the identifiers it passes through, source first.
        routes: Vec<Vec<String>>,
    },
    /// The two identifiers lie in different components of the founded terrain.
    Unreached { from: String, to: String },
}
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum DerivationCapacitanceRefusal {
    #[error(
        "the circuit carries no site with an empty incidence: there is no terrain to radiate from"
    )]
    NoTerrain,
    #[error("1-cell {0:?} does not carry an oriented two-ended boundary and is not a passage")]
    UnorientedPassage(CausalCellId),
    #[error(
        "the source population carries {sources} artifacts and the circuit was founded from {derivations}"
    )]
    SourceDoesNotMatchCircuit { sources: usize, derivations: usize },
    #[error(
        "artifact {0} declares a key the circuit does not carry: the aperture key rule has drifted"
    )]
    KeyNotInCircuit(String),
    #[error("identifier {0} is not a site of this circuit")]
    UnknownIdentifier(String),
    /// The law returned incomplete coverage and named no chronology at which the missing sites
    /// would have arrived. A site is unreturned only because its arrival was deferred, and a
    /// deferred arrival carries its chronology, so an empty testimony contradicts the law.
    #[error(
        "{unreturned} reachable sites did not return at horizon {horizon} and the law deposited no deferred chronology for any of them"
    )]
    UnreturnedSiteWithoutTestimony { unreturned: usize, horizon: u64 },
    /// A growth returned no further site, or the growths exceeded the reachable population. Both
    /// are the same broken theorem: the largest chronology the law deposited for an unreturned
    /// reachable site is that site's own earliest arrival, so growing to it must return it.
    #[error(
        "growth {growths} from horizon {horizon} to {named} returned no further site; the reachable population is {reachable} and bounds the growths"
    )]
    HorizonGrowthReturnedNothing {
        reachable: usize,
        growths: usize,
        horizon: u64,
        named: u64,
    },
    /// Conducting at the computed fixed point did not return the circuit whole. The fixed point is
    /// the largest arrival chronology the law itself returned, so this cannot happen unless the
    /// radiation is not monotone in its horizon.
    #[error(
        "the fixed point {least_sufficient} returned {returned} of {reachable} reachable sites"
    )]
    HorizonFixedPointIsNotSufficient {
        least_sufficient: u64,
        returned: usize,
        reachable: usize,
    },
    /// Conducting one chronology **below** the fixed point returned the circuit whole, so the
    /// reported horizon is larger than the material requires. This is the falsifier for the claim
    /// that the returned horizon is least, and it fires from the law rather than from a foil.
    #[error(
        "the whole reachable population of {reachable} returned at horizon {below}, one below the reported fixed point {least_sufficient}"
    )]
    HorizonFixedPointIsNotLeast {
        least_sufficient: u64,
        below: u64,
        reachable: usize,
    },
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
        // The tokenizer is `derivation_atlas`'s, called and not restated. A hand copy of the old
        // single-class `split` sat here until 2026-08-09, and its measured consequence was that
        // `source_separation` returned `None` for `contrapose!` while locating `contrapose`.
        for token in crate::derivation_atlas::identifier_tokens(read) {
            located.entry(token).or_default().insert(at);
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

    /// Every 0-cell of the circuit, whether or not the current reaches it.
    pub fn site_count(&self) -> usize {
        self.site_of.len()
    }

    /// The population the circuit's own forward walk reaches from its terrain. **This, and not the
    /// site count, is what a horizon has to cover**, and it is what bounds the growths.
    pub fn reachable_sites(&self) -> usize {
        self.reachable.len()
    }

    /// The largest characteristic delay any founded passage carries. A receiver coordinate of the
    /// delay law, returned so a caller declaring its own horizon can see the scale it is declaring
    /// against.
    pub fn longest_characteristic_delay(&self) -> u64 {
        self.law
            .passages()
            .map(|passage| passage.characteristic_delay)
            .max()
            .unwrap_or(0)
    }

    /// The terrain, as the transport law addresses it.
    fn source_sites(&self) -> LocalSet<ReceiverCurrentSiteId> {
        self.terrain.iter().map(|name| self.site_of[name]).collect()
    }

    /// The site this identifier is addressed by, and the identifier a site carries.
    ///
    /// Both directions, because a route is asked in identifiers and conducted in sites, and a
    /// returned route that cannot be read back into identifiers is a route the caller cannot use.
    pub fn site_of(&self, identifier: &str) -> Option<ReceiverCurrentSiteId> {
        self.site_of.get(identifier).copied()
    }

    /// **Every identifier the mapping carries**, in canonical order.
    ///
    /// Read the sites off the mapping; do not reconstruct them from the material. The 0-cell key is
    /// the aperture's, not the caller's — under `DerivationIdentity::ByRoute` it is
    /// `name#ordinal`, and under a founded statement incidence a statement carries a transformed
    /// key. A driver that rebuilds candidate names from `Derivation` fields and keeps the ones that
    /// resolve **silently drops every cell whose key the aperture rewrote**, and then reports the
    /// remainder as a reading of the circuit. Measured 2026-08-14: doing exactly that made two of
    /// four declared apertures return `0 joined` out of a site population it never asked about.
    pub fn identifiers(&self) -> Vec<&str> {
        self.site_of.keys().map(String::as_str).collect()
    }

    /// The identifier a site carries. Inverse of [`Self::site_of`].
    pub fn name_of(&self, site: ReceiverCurrentSiteId) -> Option<&str> {
        self.name_of.get(&site).map(String::as_str)
    }

    /// **The route between two named entities.**
    ///
    /// Both endpoints are named by the caller at call time. The law forms the complete
    /// reverse-reachable population of `to`, radiates from `from`, and returns the exact number of
    /// minimal-arrival routes — computed from the factorized arrival body, without enumerating
    /// them — beside the routes themselves, read back into identifiers.
    ///
    /// **The organ this composes has been exact and unreachable since it was built.**
    /// `ExactReceiverCurrentLaw::radiate` takes arbitrary source *and* target sets and returns
    /// `witness_paths_to`, `witness_section_to` and `exact_path_population`; measured 2026-08-14,
    /// every one of its six call sites was inside `#[cfg(test)]`, and the only production caller
    /// anywhere used the targetless `radiate_to_horizon` and took the **count**. The machine
    /// computed exactly how many routes reached a target and had never once asked for one.
    ///
    /// An endpoint the terrain does not carry is [`DerivationCapacitanceRefusal::UnknownIdentifier`].
    /// A target the radiation does not return is [`RouteReading::Unreached`], **named** — two
    /// entities in different components of the founded terrain is a fact about the terrain, and an
    /// empty vector would report it as an absence of routes rather than an absence of a join.
    pub fn route(
        &self,
        from: &str,
        to: &str,
    ) -> Result<RouteReading, DerivationCapacitanceRefusal> {
        let source = self
            .site_of(from)
            .ok_or_else(|| DerivationCapacitanceRefusal::UnknownIdentifier(from.to_owned()))?;
        let target = self
            .site_of(to)
            .ok_or_else(|| DerivationCapacitanceRefusal::UnknownIdentifier(to.to_owned()))?;

        let radiation = self
            .law
            .radiate(LocalSet::from([source]), LocalSet::from([target]))?;
        if !radiation.returned_targets.contains(&target) {
            return Ok(RouteReading::Unreached {
                from: from.to_owned(),
                to: to.to_owned(),
            });
        }

        let population = radiation.exact_path_population(target);
        let routes = radiation
            .witness_paths_to(target)?
            .into_iter()
            .map(|witness| {
                witness
                    .sites
                    .into_iter()
                    .map(|site| {
                        self.name_of(site)
                            .map(str::to_owned)
                            .unwrap_or_else(|| format!("{site:?}"))
                    })
                    .collect()
            })
            .collect();

        Ok(RouteReading::Reached {
            from: from.to_owned(),
            to: to.to_owned(),
            population,
            routes,
        })
    }

    /// How many reachable sites return when the **caller** declares the horizon.
    ///
    /// This is the receiver-declared face of the same conduct [`Self::read`] performs at the law's
    /// own fixed point. A caller that wants to know what a horizon of its own choosing costs asks
    /// here and compares against [`Self::reachable_sites`]; nothing is truncated silently, because
    /// what did not return is exactly what the difference names.
    pub fn returned_at_horizon(&self, horizon: u64) -> Result<usize, DerivationCapacitanceRefusal> {
        Ok(self
            .law
            .radiate_to_horizon(self.source_sites(), horizon)?
            .returned_targets
            .len())
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
                .map(|head| results_of.get(head.as_str()).cloned().unwrap_or_default())
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
                CapacityLaw::DistinguishableResults => {
                    distinguishable.get(name).map_or(0, BTreeSet::len).max(1)
                }
                CapacityLaw::OccurrenceMultiplicity => {
                    occurrences.get(name.as_str()).copied().unwrap_or(0).max(1) as usize
                }
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
        let site = *self.site_of.get(identifier).ok_or_else(|| {
            DerivationCapacitanceRefusal::UnknownIdentifier(identifier.to_owned())
        })?;
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
        let carried = self.capacity(identifier).ok_or_else(|| {
            DerivationCapacitanceRefusal::UnknownIdentifier(identifier.to_owned())
        })?;
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

    /// Grow the chronology horizon onto the transport law's own fixed point.
    ///
    /// **Nothing here chooses a horizon and nothing doubles one.** The growth starts at zero, where
    /// only the terrain departs, and every later horizon is a chronology the law itself deposited:
    /// a reachable site fails to return only because its arrival crossed the
    /// `arrival_chronology > horizon` gate, and that gate deposits the arrival — with its
    /// chronology — as deferred testimony. Growing to the largest such chronology therefore returns
    /// at least the unreturned site whose earliest arrival is smallest, because that site's
    /// earliest-arrival predecessor has a strictly earlier arrival and so has already returned.
    ///
    /// Three properties of `receiver_current::radiate_to_horizon` make this a terminating law
    /// rather than a budget, and each is a statement about that owner:
    ///
    /// ```text
    ///   every passage delay is positive     characteristic_delay is refused at zero and
    ///                                       passage_delay = characteristic_delay + rounds - 1
    ///   so each site departs at most once   the schedule is popped in ascending chronology and a
    ///                                       recorded arrival is replaced only by a strictly
    ///                                       earlier one, which is impossible after the pop
    ///   so the horizon is monotone          a larger horizon reproduces the smaller run exactly
    ///                                       below it, since the horizon is read only at the two
    ///                                       `> horizon` comparisons
    /// ```
    ///
    /// Each growth returns at least one further reachable site, so the **material** bounds the
    /// growths by its own forward-reachable population. Exceeding that bound is a broken theorem
    /// and returns [`DerivationCapacitanceRefusal::HorizonGrowthReturnedNothing`]; it is not a
    /// budget overrun and there is no schedule to blame it on.
    ///
    /// The horizon the growth stops at is then **contracted** onto the fixed point: the largest
    /// arrival chronology the law returned over the reachable population. Both sides of that being
    /// least are conducted rather than argued — complete at the fixed point, strictly incomplete
    /// one chronology below it.
    fn grow_to_fixed_point(
        &self,
        sources: &LocalSet<ReceiverCurrentSiteId>,
    ) -> Result<(ExactReceiverCurrentRadiation, HorizonFixedPoint), DerivationCapacitanceRefusal>
    {
        let reachable = self.reachable.len();
        let growth_bound = reachable.saturating_sub(1);

        let mut horizon = 0u64;
        let mut radiation = self.law.radiate_to_horizon(sources.clone(), horizon)?;
        let mut grown_through = vec![horizon];
        let mut returned_at = vec![radiation.returned_targets.len()];

        while radiation.returned_targets.len() < reachable {
            let named = radiation
                .deferred_arrivals
                .iter()
                .filter(|arrival| !radiation.returned_targets.contains(&arrival.site))
                .map(|arrival| arrival.chronology)
                .max();
            let Some(named) = named else {
                return Err(
                    DerivationCapacitanceRefusal::UnreturnedSiteWithoutTestimony {
                        unreturned: reachable - radiation.returned_targets.len(),
                        horizon,
                    },
                );
            };
            let grown = self.law.radiate_to_horizon(sources.clone(), named)?;
            if named <= horizon
                || grown.returned_targets.len() <= radiation.returned_targets.len()
                || grown_through.len() > growth_bound
            {
                return Err(DerivationCapacitanceRefusal::HorizonGrowthReturnedNothing {
                    reachable,
                    growths: grown_through.len(),
                    horizon,
                    named,
                });
            }
            horizon = named;
            radiation = grown;
            grown_through.push(horizon);
            returned_at.push(radiation.returned_targets.len());
        }

        // The fixed point. Every reachable site's arrival chronology is what the law returned, and
        // the largest of them is the least sufficient horizon exactly: one below it, the site
        // carrying that maximum crosses the law's own deferral gate and cannot return.
        let least_sufficient = self
            .reachable
            .iter()
            .filter_map(|name| radiation.arrivals.get(&self.site_of[name]))
            .map(|arrival| arrival.chronology)
            .max()
            .unwrap_or(0);

        let at_fixed_point = self
            .law
            .radiate_to_horizon(sources.clone(), least_sufficient)?;
        let returned_at_fixed_point = at_fixed_point.returned_targets.len();
        if returned_at_fixed_point != reachable {
            return Err(
                DerivationCapacitanceRefusal::HorizonFixedPointIsNotSufficient {
                    least_sufficient,
                    returned: returned_at_fixed_point,
                    reachable,
                },
            );
        }

        // The other side, conducted. A horizon law that reported a horizon larger than the material
        // required would return the whole population here, and this is where it would be caught.
        let returned_one_below = match least_sufficient.checked_sub(1) {
            None => None,
            Some(below) => {
                let under = self.returned_at_horizon(below)?;
                if under >= reachable {
                    return Err(DerivationCapacitanceRefusal::HorizonFixedPointIsNotLeast {
                        least_sufficient,
                        below,
                        reachable,
                    });
                }
                Some(under)
            }
        };

        Ok((
            at_fixed_point,
            HorizonFixedPoint {
                least_sufficient,
                reachable_sites: reachable,
                returned_at_fixed_point,
                returned_one_below,
                grown_through,
                returned_at,
                growth_bound,
            },
        ))
    }

    /// Conduct the circuit and read the delay population back.
    ///
    /// The horizon is the transport law's own fixed point — see [`Self::grow_to_fixed_point`] —
    /// and the reading carries the certificate that it is the least sufficient one.
    pub fn read(&self) -> Result<CapacitanceReading, DerivationCapacitanceRefusal> {
        let sources = self.source_sites();

        let (radiation, horizon_fixed_point) = self.grow_to_fixed_point(&sources)?;
        let horizon = horizon_fixed_point.least_sufficient;

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
            horizon_fixed_point,
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

/// A declared control whose **branch population doubles per rung**, so its completion chronology is
/// exponential in the rung count while its site count is linear in it.
///
/// `base` terrain symbols are recruited by the first rung's two declarations; every later rung's
/// two declarations recruit the previous rung's two. Every declaration proves the same result, so
/// the result-receiver separates no onward head and every capacity is one.
///
/// Predicted completion chronology, stated from the construction before any material is read. The
/// terrain departs at chronology zero into a fan-out of two, so rung one arrives at `2` carrying
/// the whole terrain population; thereafter a rung's co-present demand is twice the population it
/// carries and its capacity is one, so its whole demand becomes dilation:
///
/// ```text
///   population(rung k) = base * 2^(k-1)
///   arrival(rung 1)    = 2
///   arrival(rung k)    = arrival(rung k-1) + 2 * population(rung k-1)
///                      = 2 + base * (2^k - 2)          =  doubling_ladder_completion
/// ```
///
/// over `base + 2*rungs` sites. **This is the falsifier for `site_count * longest_delay` as a
/// horizon.** That product was the excised law's starting guess, and here it is smaller than the
/// chronology the circuit actually needs by a factor that grows without bound in `rungs`.
pub fn doubling_ladder(base: usize, rungs: usize) -> Vec<Derivation> {
    let mut population = Vec::new();
    for rung in 1..=rungs {
        let recruited: Vec<String> = if rung == 1 {
            (0..base).map(|at| format!("base{at}")).collect()
        } else {
            ['a', 'b']
                .into_iter()
                .map(|hand| format!("rung{}{hand}", rung - 1))
                .collect()
        };
        let borrowed: Vec<&str> = recruited.iter().map(String::as_str).collect();
        for hand in ['a', 'b'] {
            population.push(control(
                &format!("rung{rung}{hand}"),
                "one result",
                &borrowed,
            ));
        }
    }
    population
}

/// The chronology [`doubling_ladder`] is predicted to complete at, computed from the construction
/// rather than from a reading: `2 + base*(2^rungs - 2)`.
pub fn doubling_ladder_completion(base: u64, rungs: u32) -> u64 {
    if rungs == 0 {
        return 0;
    }
    2 + base * (2u64.pow(rungs) - 2)
}

/// The horizon the **excised** law would have reported: a guess of `site_count * longest_delay`,
/// doubled until the circuit returns whole.
///
/// Carried here, in the module the schedule was cut from, so the difference it made can be
/// conducted rather than remembered. It takes the coverage predicate as a closure, which is
/// [`CapacitanceMapping::returned_at_horizon`] against
/// [`CapacitanceMapping::reachable_sites`] at every call site.
///
/// Returns the horizon it stops at and the number of doublings it took, or `None` if sixty-four
/// doublings did not suffice — which is the state the excised
/// `HORIZON_DOUBLINGS = 64` refusal was written for and which **cannot occur**: from any positive
/// guess, `saturating_mul(2)` reaches `u64::MAX` inside sixty-four steps.
pub fn excised_doubling_schedule(
    site_count: usize,
    longest_characteristic_delay: u64,
    mut covers: impl FnMut(u64) -> bool,
) -> Option<(u64, u32)> {
    let mut horizon = (site_count as u64)
        .saturating_mul(longest_characteristic_delay)
        .max(1);
    let mut doublings = 0u32;
    while !covers(horizon) {
        if doublings >= 64 {
            return None;
        }
        horizon = horizon.saturating_mul(2);
        doublings += 1;
    }
    Some((horizon, doublings))
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
    use crate::derivation_atlas::{
        RecruitmentCoefficient, StatementIncidence, found_circuit, read_derivation,
    };

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

    // ------------------------------------------------------------ the route between two entities

    /// A chain `alpha -> beta -> gamma`: each derivation recruits the one before it, so the terrain
    /// runs symbol to derivation and a route from the first to the last must pass through the
    /// middle. **Both endpoints are named at call time and the route is longer than two steps** —
    /// the two things every existing route API in this tree could not do.
    fn chain() -> Vec<Derivation> {
        vec![
            control("alpha", "alpha_holds", &[]),
            control("beta", "beta_holds", &["alpha"]),
            control("gamma", "gamma_holds", &["beta"]),
        ]
    }

    fn chain_mapping(derivations: &[Derivation]) -> CapacitanceMapping {
        CapacitanceMapping::found(
            &circuit_of(derivations, CircuitAperture::DEPOSITED_READER),
            derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds a passage ecology")
    }

    #[test]
    fn a_route_is_returned_between_two_endpoints_the_caller_names() {
        let derivations = chain();
        let mapping = chain_mapping(&derivations);

        let reading = mapping.route("alpha", "gamma").expect("both are sites");
        let RouteReading::Reached {
            from,
            to,
            population,
            routes,
        } = reading
        else {
            panic!("alpha and gamma are joined by the chain: {reading:?}");
        };
        assert_eq!(from, "alpha");
        assert_eq!(to, "gamma");

        // The exact count is taken without enumerating, and the enumeration must agree with it.
        assert_eq!(
            population,
            BigUint::from(routes.len()),
            "the factorized population disagrees with the witnesses it factorizes"
        );
        assert!(!routes.is_empty());

        // Longer than two steps, and the constituent it crossed is named rather than supplied.
        let longest = routes.iter().map(Vec::len).max().unwrap();
        assert!(
            longest > 2,
            "a two-step route is what the existing API already returned: {routes:?}"
        );
        for route in &routes {
            assert_eq!(route.first().map(String::as_str), Some("alpha"));
            assert_eq!(route.last().map(String::as_str), Some("gamma"));
            assert!(
                route.iter().any(|step| step == "beta"),
                "the route does not name what it crossed: {route:?}"
            );
        }
    }

    /// The control that makes the reading an instrument: two entities in **different components**
    /// return the fact by name, not an empty vector. Without this the reached case cannot be
    /// distinguished from a terrain that joins nothing.
    #[test]
    fn two_entities_in_different_components_return_unreached_by_name() {
        let mut derivations = chain();
        derivations.push(control("island", "island_holds", &[]));
        let mapping = chain_mapping(&derivations);

        assert!(
            mapping.site_of("island").is_some(),
            "the island is a site; it is simply not joined"
        );
        assert_eq!(
            mapping.route("alpha", "island").expect("both are sites"),
            RouteReading::Unreached {
                from: "alpha".to_owned(),
                to: "island".to_owned(),
            }
        );
        // And the joined pair on the same terrain still routes, so the refusal is about the pair.
        assert!(matches!(
            mapping.route("alpha", "gamma").unwrap(),
            RouteReading::Reached { .. }
        ));
    }

    #[test]
    fn an_endpoint_the_terrain_does_not_carry_is_refused_by_name() {
        let derivations = chain();
        let mapping = chain_mapping(&derivations);
        assert!(matches!(
            mapping.route("alpha", "nowhere"),
            Err(DerivationCapacitanceRefusal::UnknownIdentifier(name)) if name == "nowhere"
        ));
        // And the two directions of the site map are inverse on every site the terrain carries.
        for name in ["alpha", "beta", "gamma"] {
            let site = mapping.site_of(name).expect("a site");
            assert_eq!(mapping.name_of(site), Some(name));
        }
    }

    // ------------------------------------------------------------ the mapping is read, not declared

    #[test]
    fn the_passage_orientation_is_read_from_the_founded_boundary_and_agrees_with_the_recruitment_key()
     {
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
            assert!(
                passages
                    .iter()
                    .any(|passage| passage.tail == vertex && &passage.head == derivation)
            );
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
            let shared = reading
                .site("sharedTerrain")
                .expect("the shared terrain is a site");
            assert_eq!(shared.service_rounds(), vec![BigUint::from(arms)]);
            let private = reading
                .site("private0")
                .expect("a private symbol is a site");
            assert_eq!(private.service_rounds(), vec![BigUint::one()]);

            let classes = reading.dilation_classes();
            assert!(
                !classes.is_vacuous(),
                "the prediction is two classes at arms={arms}"
            );
            assert_eq!(
                classes
                    .by_service_rounds
                    .keys()
                    .cloned()
                    .collect::<Vec<_>>(),
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
            classes
                .by_service_rounds
                .keys()
                .cloned()
                .collect::<Vec<_>>(),
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
            derivations.push(control(&format!("head{arm}"), "one result", &["relay"]));
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
            derivations.push(control(&format!("tight{arm}"), "one result", &["narrow"]));
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
        assert_eq!(
            source_separation(PRODUCTION_ROUTE, "KernelWitness"),
            Some(2)
        );
        assert_eq!(source_separation(PRODUCTION_ROUTE, "Soma"), Some(1));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "Prop"), Some(0));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "exactCarrier"), Some(0));
        assert_eq!(source_separation(PRODUCTION_ROUTE, "assumption"), Some(1));
        // `end Soma` is skipped exactly as the atlas skips it, so the closing line never supplies a
        // nearer location than `namespace Soma` does.
        assert_eq!(
            source_separation(RESEARCH_ROUTE, "exact_chart_carry"),
            Some(1)
        );
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

    // ------------------------------------------------------------ the horizon is the law's own

    fn mapping_of(derivations: &[Derivation]) -> CapacitanceMapping {
        let circuit = circuit_of(derivations, CircuitAperture::DEPOSITED_READER);
        CapacitanceMapping::found(
            &circuit,
            derivations,
            &[],
            CapacityLaw::DistinguishableResults,
            CharacteristicDelayLaw::Uniform,
        )
        .expect("the circuit founds")
    }

    #[test]
    fn the_horizon_is_the_least_chronology_at_which_the_circuit_returns_whole() {
        for derivations in [
            one_result_star(9),
            many_result_star(5),
            disjoint_terrain(6),
            doubling_ladder(2, 5),
            doubling_ladder(4, 4),
        ] {
            let mapping = mapping_of(&derivations);
            let reading = mapping.read().expect("the current conducts");
            let fixed = &reading.horizon_fixed_point;

            assert_eq!(reading.horizon, fixed.least_sufficient);
            assert_eq!(fixed.returned_at_fixed_point, fixed.reachable_sites);
            assert!(fixed.is_least(), "{fixed:?}");

            // Both halves conducted rather than argued, through the caller-declared face.
            assert_eq!(
                mapping
                    .returned_at_horizon(fixed.least_sufficient)
                    .expect("conducts"),
                fixed.reachable_sites
            );
            if let Some(below) = fixed.least_sufficient.checked_sub(1) {
                let under = mapping.returned_at_horizon(below).expect("conducts");
                assert_eq!(Some(under), fixed.returned_one_below);
                assert!(
                    under < fixed.reachable_sites,
                    "horizon {} is not least: {under} of {} returned at {below}",
                    fixed.least_sufficient,
                    fixed.reachable_sites
                );
            } else {
                assert_eq!(fixed.returned_one_below, None);
            }

            // And the horizon is exactly the largest arrival the reading itself carries, so nothing
            // outside the returned population decides it.
            let largest = reading
                .sites
                .iter()
                .filter_map(|site| site.arrival_chronology)
                .max()
                .expect("the terrain arrives");
            assert_eq!(reading.horizon, largest);
        }
    }

    #[test]
    fn every_grown_horizon_is_a_chronology_the_law_itself_deposited_and_each_returns_more() {
        let derivations = doubling_ladder(3, 4);
        let mapping = mapping_of(&derivations);
        let reading = mapping.read().expect("the current conducts");
        let fixed = &reading.horizon_fixed_point;

        assert_eq!(fixed.grown_through.first(), Some(&0));
        assert_eq!(fixed.grown_through.len(), fixed.returned_at.len());
        assert!(
            fixed.growths() >= 1,
            "a ladder cannot return whole at horizon zero: {fixed:?}"
        );
        assert!(
            fixed.growths() <= fixed.growth_bound,
            "the material bounds the growths: {fixed:?}"
        );
        for pair in fixed.grown_through.windows(2) {
            assert!(pair[1] > pair[0], "the growth is strict: {fixed:?}");
        }
        for pair in fixed.returned_at.windows(2) {
            assert!(
                pair[1] > pair[0],
                "every growth returns at least one further site: {fixed:?}"
            );
        }
        // Each grown horizon is a chronology at which some site actually arrives — that is what
        // makes it the law's testimony rather than an invented number.
        let arrivals: BTreeSet<u64> = reading
            .sites
            .iter()
            .filter_map(|site| site.arrival_chronology)
            .collect();
        for grown in &fixed.grown_through {
            assert!(
                arrivals.contains(grown),
                "horizon {grown} is not an arrival chronology of this circuit: {arrivals:?}"
            );
        }
    }

    #[test]
    fn the_ladder_arrives_exponentially_past_the_site_count_the_excised_guess_used() {
        // The excised law started at `site_count * longest_characteristic_delay`. The ladder's site
        // count is linear in its rungs and its completion chronology is exponential in them, so the
        // guess undershoots by a factor that grows without bound.
        let mut undershoot = Vec::new();
        for rungs in 2usize..=7 {
            let derivations = doubling_ladder(2, rungs);
            let mapping = mapping_of(&derivations);
            let reading = mapping.read().expect("the current conducts");

            assert_eq!(
                reading.horizon,
                doubling_ladder_completion(2, rungs as u32),
                "the construction predicted this chronology before the reading was taken"
            );
            assert_eq!(mapping.site_count(), 2 + 2 * rungs);
            assert_eq!(mapping.longest_characteristic_delay(), 1);

            let guess = (mapping.site_count() as u64) * mapping.longest_characteristic_delay();
            // The crossover is measured rather than assumed: at two rungs the guess is exactly
            // right, and from three rungs on it is short by a margin that doubles with the rung.
            if rungs >= 3 {
                assert!(
                    guess < reading.horizon,
                    "rungs={rungs}: guess {guess} did not undershoot {}",
                    reading.horizon
                );
            }
            undershoot.push(reading.horizon - guess);
        }
        assert_eq!(undershoot[0], 0, "two rungs is where the guess is exact");
        assert!(
            undershoot.windows(2).all(|pair| pair[1] > pair[0]),
            "the undershoot must grow with the rung count: {undershoot:?}"
        );
        assert_eq!(undershoot, vec![0, 6, 20, 50, 112, 238]);
    }

    #[test]
    fn two_circuits_the_excised_schedule_reported_alike_have_different_fixed_points() {
        // One site count, one longest delay, so the excised law's starting guess and every doubling
        // of it are identical. The two circuits complete at different chronologies and the schedule
        // could not say so: it reports the band, and the band is a receiver coordinate of the
        // schedule rather than of the material.
        let left = doubling_ladder(2, 5);
        let right = doubling_ladder(4, 4);

        let left_mapping = mapping_of(&left);
        let right_mapping = mapping_of(&right);
        assert_eq!(left_mapping.site_count(), right_mapping.site_count());
        assert_eq!(
            left_mapping.longest_characteristic_delay(),
            right_mapping.longest_characteristic_delay()
        );

        let schedule = |mapping: &CapacitanceMapping| {
            excised_doubling_schedule(
                mapping.site_count(),
                mapping.longest_characteristic_delay(),
                |horizon| {
                    mapping.returned_at_horizon(horizon).expect("conducts")
                        >= mapping.reachable_sites()
                },
            )
            .expect("sixty-four doublings always suffice")
        };

        let left_reported = schedule(&left_mapping);
        let right_reported = schedule(&right_mapping);
        assert_eq!(
            left_reported.0, right_reported.0,
            "the two circuits must be indistinguishable to the excised schedule"
        );

        let left_fixed = left_mapping.read().expect("conducts").horizon;
        let right_fixed = right_mapping.read().expect("conducts").horizon;
        assert_ne!(
            left_fixed, right_fixed,
            "the fixed point must separate what the schedule could not"
        );
        assert_eq!(left_fixed, doubling_ladder_completion(2, 5));
        assert_eq!(right_fixed, doubling_ladder_completion(4, 4));
        assert!(left_reported.0 > left_fixed && left_reported.0 > right_fixed);
    }

    #[test]
    fn the_excised_sixty_four_doubling_refusal_could_not_have_fired() {
        // The refusal was written for a schedule that never covers. `saturating_mul(2)` from any
        // positive guess reaches `u64::MAX` inside sixty-four steps, and at `u64::MAX` the horizon
        // gates nothing, so the whole reachable population returns.
        for guess in [1u64, 3, 22, 121, u64::MAX / 3] {
            let mut horizon = guess;
            for _ in 0..64 {
                horizon = horizon.saturating_mul(2);
            }
            assert_eq!(horizon, u64::MAX);
        }
        for derivations in [one_result_star(9), doubling_ladder(2, 6)] {
            let mapping = mapping_of(&derivations);
            assert_eq!(
                mapping.returned_at_horizon(u64::MAX).expect("conducts"),
                mapping.reachable_sites(),
                "at the saturated horizon nothing can still be missing"
            );
            let (_, doublings) = excised_doubling_schedule(
                mapping.site_count(),
                mapping.longest_characteristic_delay(),
                |horizon| {
                    mapping.returned_at_horizon(horizon).expect("conducts")
                        >= mapping.reachable_sites()
                },
            )
            .expect("the schedule always covers");
            assert!(doublings < 64, "{doublings} doublings");
        }
    }

    #[test]
    fn the_caller_declared_horizon_returns_less_than_the_fixed_point_does() {
        // The control that can fail: a horizon below the fixed point must leave sites unreturned,
        // and one at or above it must not. A `returned_at_horizon` that ignored its argument, or a
        // fixed point that overstated the material, breaks this in opposite directions.
        let derivations = doubling_ladder(2, 4);
        let mapping = mapping_of(&derivations);
        let fixed = mapping.read().expect("conducts").horizon;
        let reachable = mapping.reachable_sites();

        let mut returned: Vec<usize> = Vec::new();
        for horizon in 0..=fixed {
            returned.push(mapping.returned_at_horizon(horizon).expect("conducts"));
        }
        assert!(returned.windows(2).all(|pair| pair[1] >= pair[0]));
        assert_eq!(*returned.last().expect("the fixed point"), reachable);
        assert!(
            returned[..returned.len() - 1]
                .iter()
                .all(|carried| *carried < reachable)
        );
        assert_eq!(
            mapping
                .returned_at_horizon(fixed.saturating_mul(4))
                .expect("conducts"),
            reachable
        );
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
