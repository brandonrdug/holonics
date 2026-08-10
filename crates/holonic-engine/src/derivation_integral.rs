//! Integration through reflection on a derivation circuit: what two routes accumulated, and the
//! holonomy their disagreement retains.
//!
//! ## What this composes, and why it is one organ and not three
//!
//! Three modules were built in isolation and had no consumer anywhere in the tree.
//! [`crate::running_integral`] carries the exact running sum of a 1-cochain along a path and the
//! retained residual of a compared pair. [`crate::leader_quadrature`] carries an independent
//! integrator whose return is a FOUND/RIDE lineage with retained refounding obstructions.
//! [`crate::causal_reflection`] carries a response on a symmetric lattice whose two faces determine
//! each other exactly when the response is structurally causal. This module puts all three on the
//! one carrier that now exists — [`ConditionedCircuit`], the conditioned body's own production read
//! as a `GradedCausalComplex` with every cell traced back to the passage that founded it.
//!
//! A **route** here is a chain of recruitments between two declarations. Three species occur, and
//! each is a real thing a derivation does:
//!
//! ```text
//!   D  -[s]->  E     both declarations recruit the identifier s; the route crosses it
//!   D  -[|- S]-> E   both declarations reach the statement S; the route crosses the result
//!   D  ----->  E     E is itself an identifier D recruited; one step, no join
//! ```
//!
//! The third exists only when a declaration is **both a result and a resource**, and that is not a
//! hypothetical on the deposited material: `formal_carry` is declared by seven artifacts and
//! recruited by six other declarations. That collision is what makes the 1-skeleton non-bipartite,
//! and it is where the winding lives.
//!
//! ## The two accumulation rules, and the fact that separates them
//!
//! Both are read off the recruitment multiset the export codec already recovered, and both are
//! exact integers. The whole content of this module is that they behave differently:
//!
//! ```text
//!   RouteLoad         every 1-cell carries the whole recruitment load Λ(D) of the declaration
//!                     at its HEAD.   w(D<-s) = Λ(D)   and   w(D|-S) = Λ(D).
//!   RecruitmentLoad   a recruitment cell carries what THAT recruitment carried, m(D,s); a reach
//!                     cell carries the route's whole load.  w(D<-s) = m(D,s),  w(D|-S) = Λ(D).
//! ```
//!
//! [`AccumulationRule::RouteLoad`] is head-determined, so it **admits a potential exactly when no
//! declaration is ever recruited** — take `f = Λ` on declaration vertices and `f = 0` elsewhere,
//! and `w(e) = f(head) - f(tail)` holds on every cell whose tail is a pure symbol or statement. The
//! demand fails at exactly one place: a cell `D<-E` where `E` is itself a declaration, because there
//! `f(E) = Λ(E)` is not zero. So:
//!
//! > **The holonomy of `RouteLoad` around a recruited declaration is exactly minus that
//! > declaration's own load.** Travelling to `E` as a resource costs nothing of `E`'s derivation;
//! > travelling to it as a result costs its whole load. The difference is `Λ(E)`, and it is the
//! > winding.
//!
//! This is not asserted, it is measured: [`potential_over`] walks a spanning tree of the whole
//! 1-skeleton and **tests every chord**, retaining each failure as a [`ChordObstruction`] with its
//! exact residual and the passages that founded the cell. On a circuit with no recruited declaration
//! the retained population is empty with a cycle rank in the hundreds — the test could have failed
//! at every one of them and did not.
//!
//! [`AccumulationRule::RecruitmentLoad`] is not head-determined and winds on both circuits. Carrying
//! both is what makes the returned exactness belong to the rule rather than to the circuit's shape.
//!
//! ## The same holonomy, three ways
//!
//! Every compared pair returns its residual through three disjoint carriers, and
//! [`RouteDisagreement::three_readings_agree`] is the equality:
//!
//! ```text
//!   running_integral    total(left) - total(right)                            in Z
//!   leader_quadrature   path_disagreement(leader(left), leader(right))        in Q
//!   causal_reflection   Σ_{n>0} 2·absorptive[n]  of the pair's response        in Q
//! ```
//!
//! The leader reading is a genuine second implementation: each step becomes a unit
//! [`RationalGerm`] carrying a constant jet, and a leader grows over it under
//! [`RideDiscipline::GermBounded`] at **the law that material declares for itself** — see
//! [`leader_law`] — so every germ costs one FOUND and one RIDE of exactly one rank step, and the
//! founded axis is refounded exactly where the accumulation changed rate. [`germwise_oracle_area`]
//! grades that lineage against one antiderivative per germ, which is the cheaper implementation and
//! returns the same rational.
//!
//! The reflection reading embeds the **pair** as one response: the left route's increments at the
//! retarded indices `+1..+n`, the right route's at the advanced indices `-1..-n`, and zero at the
//! stimulus. Then a structurally causal reading of the pair means the right route accumulated
//! nothing — the pair was never two routes — so [`CausalResponse::is_causal`] is a falsifier for
//! path degeneracy, [`CausalResponse::advanced_support`] returns the second route as an exhibited
//! witness, and the [`HolomorphyWitness`]'s retained obstruction to extending over infinity **is**
//! the second route. The absorptive face is the step-by-step holonomy density and the dispersive
//! face is what the two routes shared.
//!
//! ## Aperture
//!
//! Every value is a [`BigInt`] or an exact [`Rat`]; there is no float, no tolerance, no threshold
//! and no score. [`crate::running_integral`] declares its aperture as **joinable 1-cells** — one
//! `+1` head and one `-1` tail — so a circuit founded under
//! [`RecruitmentCoefficient::Multiplicity`] is outside it and this module never integrates over
//! one. The multiplicity reading is used for one thing only, in
//! [`loads_agree_with_the_boundary`]: it is an independent implementation of the recruitment
//! multiset, and the load table is graded against it.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::algebraic::CausalCellId;
use crate::causal_reflection::{
    causality_lock, CausalReflectionError, CausalResponse, CausalityLock, FaceParity,
    HolomorphyWitness,
};
use crate::conditioned_derivation::{
    found_conditioned_circuit, ConditionedCircuit, ConditionedDerivationRefusal, Passage, PassageId,
    PassageOrigin,
};
use crate::derivation_atlas::{DerivationIdentity, RecruitmentCoefficient};
use crate::leader_quadrature::{
    germwise_oracle_area, integrate_by_leaders, path_disagreement, LeaderError, LeaderLaw,
    LeaderQuadrature, LocalJet, MaterialBoundary, RationalGerm, RideDiscipline,
};
use crate::running_integral::{
    disagreement, found_potential, running_sum, Cochain, Disagreement, Path, PathStep,
    PotentialSearch, RunningIntegral, RunningIntegralError,
};

// -------------------------------------------------------------------------------------------------
// the loads
// -------------------------------------------------------------------------------------------------

/// What each accumulation rule assigns to a 1-cell. Both are exact integers read off the
/// recruitment multiset; neither governs anything.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AccumulationRule {
    /// Every 1-cell carries the whole recruitment load of the declaration at its head.
    RouteLoad,
    /// A recruitment cell carries what that recruitment carried; a reach cell carries the whole
    /// load the route brought to its conclusion.
    RecruitmentLoad,
}

impl AccumulationRule {
    pub const fn named(self) -> &'static str {
        match self {
            Self::RouteLoad => "route-load",
            Self::RecruitmentLoad => "recruitment-load",
        }
    }
}

/// The recruitment multiset of a circuit, recomputed the way `found_circuit` sums it.
///
/// A declaration never recruits itself, so that term is dropped here exactly as the founding drops
/// it. [`loads_agree_with_the_boundary`] grades this against the complex's own boundary
/// coefficients under a multiplicity aperture, which is an independent implementation of the same
/// multiset.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CircuitLoads {
    pub schema: String,
    pub identity: DerivationIdentity,
    /// declaration vertex key -> recruited identifier -> exact occurrence count.
    pub recruitment: BTreeMap<String, BTreeMap<String, BigInt>>,
    /// declaration vertex key -> `Λ(D)`, the sum of its recruitment counts.
    pub route: BTreeMap<String, BigInt>,
}

impl CircuitLoads {
    /// `m(D, s)`, zero for a pair the founding carries no cell for.
    pub fn recruitment_load(&self, declaration: &str, identifier: &str) -> BigInt {
        self.recruitment
            .get(declaration)
            .and_then(|carried| carried.get(identifier))
            .cloned()
            .unwrap_or_else(BigInt::zero)
    }

    /// `Λ(D)`, zero for a vertex that is not a declaration.
    pub fn route_load(&self, declaration: &str) -> BigInt {
        self.route
            .get(declaration)
            .cloned()
            .unwrap_or_else(BigInt::zero)
    }

    /// Every declaration vertex key, in canonical order.
    pub fn declarations(&self) -> BTreeSet<&str> {
        self.route.keys().map(String::as_str).collect()
    }
}

/// The vertex key `found_circuit` gives the passage at `ordinal` under a declared identity.
fn vertex_key(identity: DerivationIdentity, passage: &Passage, ordinal: usize) -> String {
    match identity {
        DerivationIdentity::ByDeclaration => passage.derivation.name.clone(),
        DerivationIdentity::ByRoute => format!("{}#{ordinal}", passage.derivation.name),
    }
}

/// The recruitment multiset and the route loads of one circuit.
pub fn circuit_loads(circuit: &ConditionedCircuit) -> CircuitLoads {
    let identity = circuit.aperture.identity;
    let mut recruitment: BTreeMap<String, BTreeMap<String, BigInt>> = BTreeMap::new();
    for (ordinal, passage) in circuit.passages.iter().enumerate() {
        let key = vertex_key(identity, passage, ordinal);
        let slot = recruitment.entry(key).or_default();
        for (symbol, count) in &passage.derivation.recruited {
            if symbol == &passage.derivation.name {
                continue;
            }
            *slot.entry(symbol.clone()).or_insert_with(BigInt::zero) += BigInt::from(*count);
        }
    }
    let route = recruitment
        .iter()
        .map(|(key, carried)| {
            (
                key.clone(),
                carried.values().fold(BigInt::zero(), |sum, count| sum + count),
            )
        })
        .collect();
    CircuitLoads {
        schema: "holonic-engine.derivation-integral-loads.v1".to_owned(),
        identity,
        recruitment,
        route,
    }
}

/// Grade the load table against the complex's own boundary coefficients.
///
/// Only meaningful on a circuit founded under [`RecruitmentCoefficient::Multiplicity`], where the
/// boundary of a recruitment cell carries the occurrence count; `None` otherwise rather than a
/// vacuous `true`. The two readings are computed from disjoint material — one by summing the
/// derivations' own multisets, the other by reading the incidence the founding wrote — so a
/// mis-summed load shows up here.
pub fn loads_agree_with_the_boundary(circuit: &ConditionedCircuit) -> Option<bool> {
    if circuit.aperture.coefficient != RecruitmentCoefficient::Multiplicity {
        return None;
    }
    let loads = circuit_loads(circuit);
    let complex = circuit.circuit.complex();
    for ((key, symbol), cell) in circuit.circuit.recruitments() {
        let Ok(body) = complex.cell(*cell) else {
            return Some(false);
        };
        let Some(vertex) = circuit.circuit.vertices().get(key) else {
            return Some(false);
        };
        if body.boundary.coefficient(*vertex).difference() != loads.recruitment_load(key, symbol) {
            return Some(false);
        }
    }
    Some(true)
}

/// The 1-cochain a rule assigns to a circuit.
pub fn accumulation(circuit: &ConditionedCircuit, rule: AccumulationRule) -> Cochain {
    let loads = circuit_loads(circuit);
    let mut cochain = Cochain::new(1);
    for ((key, symbol), cell) in circuit.circuit.recruitments() {
        let value = match rule {
            AccumulationRule::RouteLoad => loads.route_load(key),
            AccumulationRule::RecruitmentLoad => loads.recruitment_load(key, symbol),
        };
        cochain.set(*cell, value);
    }
    for ((key, _statement), cell) in circuit.circuit.reaches() {
        cochain.set(*cell, loads.route_load(key));
    }
    cochain
}

/// Every declaration vertex that some **other** declaration recruited: the population that makes the
/// 1-skeleton non-bipartite and the only place [`AccumulationRule::RouteLoad`] can wind.
pub fn recruited_declarations(circuit: &ConditionedCircuit) -> BTreeSet<String> {
    let loads = circuit_loads(circuit);
    let declarations: BTreeSet<&str> = loads.declarations();
    let mut recruited = BTreeSet::new();
    for (key, carried) in &loads.recruitment {
        for symbol in carried.keys() {
            if symbol != key && declarations.contains(symbol.as_str()) {
                recruited.insert(symbol.clone());
            }
        }
    }
    recruited
}

/// The declaration vertices that reached one statement, under a founded statement incidence.
pub fn declarations_reaching(circuit: &ConditionedCircuit, statement: &str) -> BTreeSet<String> {
    circuit
        .circuit
        .reaches()
        .keys()
        .filter(|(_, reached)| reached == statement)
        .map(|(key, _)| key.clone())
        .collect()
}

/// The same production with every artifact **declaring** one of the named theorems removed.
///
/// Passage identities are re-indexed, because [`ConditionedCircuit::passages_founding`] resolves a
/// [`PassageId`] as an index into the passage vector; a filtered population that kept its old
/// identities would name the wrong passages. This is the structural ablation the exactness control
/// needs: removing the artifacts that declare `E` does not remove the vertex `E`, it removes every
/// 1-cell whose **head** is `E`, which is exactly the departure from head-separation.
pub fn without_declarations(
    circuit: &ConditionedCircuit,
    names: &BTreeSet<String>,
) -> Result<ConditionedCircuit, ConditionedDerivationRefusal> {
    let passages: Vec<Passage> = circuit
        .passages
        .iter()
        .filter(|passage| !names.contains(&passage.derivation.name))
        .enumerate()
        .map(|(ordinal, passage)| Passage {
            id: PassageId(ordinal as u64),
            origin: passage.origin.clone(),
            derivation: passage.derivation.clone(),
            text: passage.text.clone(),
        })
        .collect();
    found_conditioned_circuit(passages, circuit.aperture)
}

// -------------------------------------------------------------------------------------------------
// the routes
// -------------------------------------------------------------------------------------------------

/// What a route crossed between two declarations.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RouteJoin {
    /// Both declarations recruit this identifier.
    SharedRecruitment { identifier: String },
    /// Both declarations reach this statement.
    SharedStatement { statement: String },
    /// The arrival is itself an identifier the departure recruited. One step, no join.
    DirectRecruitment,
}

impl RouteJoin {
    pub fn named(&self) -> String {
        match self {
            Self::SharedRecruitment { identifier } => format!("[{identifier}]"),
            Self::SharedStatement { statement } => format!("[|- {statement}]"),
            Self::DirectRecruitment => "[direct]".to_owned(),
        }
    }
}

/// One chain of recruitments from one declaration to another, with the cells it crosses named.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Route {
    pub schema: String,
    pub from: String,
    pub to: String,
    pub join: RouteJoin,
    /// The cells crossed, by the name the founding gave them, in traversal order.
    pub cells: Vec<String>,
    pub path: Path,
}

impl Route {
    /// The route as a reader's sentence: `from -[what it crossed]-> to`.
    pub fn named(&self) -> String {
        format!("{} -{}-> {}", self.from, self.join.named(), self.to)
    }
}

fn cell_name(circuit: &ConditionedCircuit, cell: CausalCellId) -> String {
    circuit
        .circuit
        .complex()
        .cell(cell)
        .map(|body| body.name.clone())
        .unwrap_or_else(|_| format!("{cell:?}"))
}

/// A declaration vertex is the **head** of its recruitment cell, so leaving it crosses that cell
/// against its own orientation and arriving at one crosses along it.
fn two_step(
    circuit: &ConditionedCircuit,
    from_cell: CausalCellId,
    to_cell: CausalCellId,
) -> (Vec<String>, Path) {
    (
        vec![cell_name(circuit, from_cell), cell_name(circuit, to_cell)],
        Path::new([PathStep::against(from_cell), PathStep::along(to_cell)]),
    )
}

/// The route from `from` to `to` across an identifier both recruit.
pub fn route_via_recruitment(
    circuit: &ConditionedCircuit,
    from: &str,
    to: &str,
    identifier: &str,
) -> Option<Route> {
    let recruitments = circuit.circuit.recruitments();
    let departure = recruitments.get(&(from.to_owned(), identifier.to_owned()))?;
    let arrival = recruitments.get(&(to.to_owned(), identifier.to_owned()))?;
    let (cells, path) = two_step(circuit, *departure, *arrival);
    Some(Route {
        schema: "holonic-engine.derivation-route.v1".to_owned(),
        from: from.to_owned(),
        to: to.to_owned(),
        join: RouteJoin::SharedRecruitment {
            identifier: identifier.to_owned(),
        },
        cells,
        path,
    })
}

/// The route from `from` to `to` across a statement both reach.
pub fn route_via_statement(
    circuit: &ConditionedCircuit,
    from: &str,
    to: &str,
    statement: &str,
) -> Option<Route> {
    let reaches = circuit.circuit.reaches();
    let departure = reaches.get(&(from.to_owned(), statement.to_owned()))?;
    let arrival = reaches.get(&(to.to_owned(), statement.to_owned()))?;
    let (cells, path) = two_step(circuit, *departure, *arrival);
    Some(Route {
        schema: "holonic-engine.derivation-route.v1".to_owned(),
        from: from.to_owned(),
        to: to.to_owned(),
        join: RouteJoin::SharedStatement {
            statement: statement.to_owned(),
        },
        cells,
        path,
    })
}

/// The one-step route that exists exactly when `to` is an identifier `from` recruited.
pub fn route_direct(circuit: &ConditionedCircuit, from: &str, to: &str) -> Option<Route> {
    let cell = *circuit
        .circuit
        .recruitments()
        .get(&(from.to_owned(), to.to_owned()))?;
    Some(Route {
        schema: "holonic-engine.derivation-route.v1".to_owned(),
        from: from.to_owned(),
        to: to.to_owned(),
        join: RouteJoin::DirectRecruitment,
        cells: vec![cell_name(circuit, cell)],
        path: Path::new([PathStep::against(cell)]),
    })
}

/// Every identifier two declarations both recruit, in canonical order.
pub fn shared_recruitments(loads: &CircuitLoads, left: &str, right: &str) -> BTreeSet<String> {
    let (Some(here), Some(there)) = (loads.recruitment.get(left), loads.recruitment.get(right))
    else {
        return BTreeSet::new();
    };
    here.keys()
        .filter(|symbol| there.contains_key(*symbol))
        .cloned()
        .collect()
}

// -------------------------------------------------------------------------------------------------
// the compared pair
// -------------------------------------------------------------------------------------------------

/// One crossed cell with the passages that founded it and what the route accumulated over it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellProvenance {
    pub cell: String,
    pub increment: BigInt,
    /// The passages that founded this cell, named — never a bare identity.
    pub passages: Vec<String>,
}

/// How a passage is named in a returned provenance.
pub fn passage_label(passage: &Passage) -> String {
    match &passage.origin {
        PassageOrigin::Standing { source } => {
            let stem = std::path::Path::new(source)
                .file_stem()
                .map(|name| name.to_string_lossy().into_owned())
                .unwrap_or_else(|| source.clone());
            format!("{} (standing {stem})", passage.derivation.name)
        }
        PassageOrigin::Derived {
            stem,
            reaches,
            brought,
        } => format!(
            "{} (derived: stem {stem:?} brought {brought} reaching {reaches})",
            passage.derivation.name
        ),
    }
}

fn provenance(
    circuit: &ConditionedCircuit,
    integral: &RunningIntegral,
) -> Vec<CellProvenance> {
    integral
        .steps
        .iter()
        .map(|step| CellProvenance {
            cell: cell_name(circuit, step.cell),
            increment: step.increment.clone(),
            passages: circuit
                .passages_founding(step.cell)
                .into_iter()
                .map(passage_label)
                .collect(),
        })
        .collect()
}

fn rational(value: &BigInt) -> Rat {
    Rat::from_integer(value.clone())
}

/// The leader law one route's material declares for itself.
///
/// **Neither level is authored here.** Both were, until 2026-08-09:
/// `LEADER_GRAIN_RECIPROCAL: i64 = 3` and `LEADER_WITNESS_DEPTH: usize = 1`, excised for
/// `canon/THE_AUTHORED_LEVEL.md` §5.1.
///
/// - The **witness depth** is read at every tip off the jet standing there
///   ([`crate::leader_quadrature::WitnessDepth::ReadOffTheJet`]). On this module's route material
///   every germ carries a constant jet, so the rebase of a jet is itself and the material returns a
///   depth of **one** — the value the pin authored, now derived and now carried on the return as
///   `material_witness_depth` rather than declared into it. It moves the instant the material does.
/// - The **grain** is [`MaterialBoundary::declared_grain`]: the finest standing extent over
///   `jet_aperture + 2`. On unit germs carrying rank-one jets that is `1/3`, which is what the pin
///   said; the derivation is in `declared_grain`'s own doc and it is what makes every route's
///   FOUND/RIDE split a ride of exactly one rank step instead of an arrangement that happened to
///   produce one.
pub fn leader_law(material: &MaterialBoundary) -> LeaderLaw {
    LeaderLaw::read_off(material, RideDiscipline::GermBounded)
}

/// One route as material a leader can grow over: one unit germ per step, carrying that step's
/// increment as a constant jet.
///
/// The germ is chart-local and carries no absolute position, which is the representation
/// [`MaterialBoundary`] declares; the route's own order is the only lineage.
pub fn route_material(integral: &RunningIntegral) -> Result<MaterialBoundary, LeaderError> {
    let germs = integral
        .steps
        .iter()
        .map(|step| {
            RationalGerm::new(
                Rat::one(),
                LocalJet::new(vec![rational(&step.increment)])?,
            )
        })
        .collect::<Result<Vec<_>, LeaderError>>()?;
    MaterialBoundary::new(germs)
}

/// The compared pair as one response on a symmetric lattice.
///
/// Left on the retarded half, right on the advanced half, zero at the stimulus. Nothing about the
/// residual is written in: the stimulus value is zero and the residual is recovered from the
/// absorptive face.
pub fn pair_response(
    left: &RunningIntegral,
    right: &RunningIntegral,
) -> Result<CausalResponse, CausalReflectionError> {
    let half = left.steps.len().max(right.steps.len()).max(1);
    let mut values = vec![Rat::zero(); 2 * half + 1];
    for (index, step) in left.steps.iter().enumerate() {
        values[half + index + 1] = rational(&step.increment);
    }
    for (index, step) in right.steps.iter().enumerate() {
        values[half - index - 1] = rational(&step.increment);
    }
    CausalResponse::new(half as u32, Rat::one(), values)
}

/// `Σ_{n>0} 2·h_o[n]`, which is `Σ_n (h[n] - h[-n])` and therefore the residual of the pair — read
/// entirely off the odd face, never off the stimulus.
pub fn residual_from_reflection(response: &CausalResponse) -> Rat {
    let absorptive = response.absorptive_face();
    debug_assert_eq!(absorptive.parity, FaceParity::Absorptive);
    let two = Rat::from_integer(BigInt::from(2));
    absorptive
        .indices()
        .filter(|index| *index > 0)
        .fold(Rat::zero(), |sum, index| {
            sum + absorptive.value(index) * &two
        })
}

/// Two routes with the same endpoints, compared, with every carrier's return retained.
#[derive(Clone, Debug)]
pub struct RouteDisagreement {
    pub schema: String,
    pub rule: AccumulationRule,
    pub left: Route,
    pub right: Route,
    /// `running_integral`'s return: both lineages and the exact standing residual.
    pub disagreement: Disagreement,
    pub left_founding: Vec<CellProvenance>,
    pub right_founding: Vec<CellProvenance>,
    /// `leader_quadrature`'s return: the FOUND/RIDE lineage of each route.
    pub leader_left: LeaderQuadrature,
    pub leader_right: LeaderQuadrature,
    /// The independent germwise antiderivative of each route.
    pub oracle_left: Rat,
    pub oracle_right: Rat,
    /// `path_disagreement` of the two lineages: the residual, a second time.
    pub leader_residual: Rat,
    /// `causal_reflection`'s return: the pair as one response, and its law.
    pub response: CausalResponse,
    pub lock: CausalityLock,
    pub holomorphy: HolomorphyWitness,
    /// The residual recovered from the absorptive face: a third time.
    pub reflected_residual: Rat,
}

impl RouteDisagreement {
    /// The name a reader sees: both routes, joined by what they disagree about.
    pub fn named(&self) -> String {
        format!("{}   against   {}", self.left.named(), self.right.named())
    }

    /// The residual stands: this pair carries holonomy.
    pub fn stands(&self) -> bool {
        self.disagreement.stands()
    }

    pub fn residual(&self) -> &BigInt {
        &self.disagreement.residual
    }

    /// The two routes are distinguishable as chains. A pair whose cycle is zero cannot disagree on
    /// any cochain, so its agreement is vacuous and may never be read as evidence.
    pub fn routes_are_distinct(&self) -> bool {
        self.disagreement.paths_are_distinct()
    }

    /// The three carriers returned the same residual, exactly.
    pub fn three_readings_agree(&self) -> bool {
        let exact = rational(&self.disagreement.residual);
        exact == self.leader_residual && exact == self.reflected_residual
    }

    /// Each leader lineage agrees with the germwise antiderivative that grades it, and both agree
    /// with the running sum they were built from.
    pub fn leader_grades_the_running_sum(&self) -> bool {
        self.leader_left.area == self.oracle_left
            && self.leader_right.area == self.oracle_right
            && self.oracle_left == rational(&self.disagreement.left.total)
            && self.oracle_right == rational(&self.disagreement.right.total)
    }

    /// Every route both FOUNDed and RODE. A lineage that only founds has degenerated to grain-only
    /// and the ride half of the leader is present in the code and absent from the evidence.
    pub fn leader_founds_and_rides(&self) -> bool {
        self.leader_left.found_count() > 0
            && self.leader_left.ride_count() > 0
            && self.leader_right.found_count() > 0
            && self.leader_right.ride_count() > 0
    }

    /// The refounding obstructions of both lineages: where along each route the founded axis stopped
    /// predicting the material, with the exact winding residual it was wrong by.
    pub fn refoundings(&self) -> Vec<(String, usize, Rat)> {
        let mut retained = Vec::new();
        for (route, quadrature) in [
            (&self.left, &self.leader_left),
            (&self.right, &self.leader_right),
        ] {
            for obstruction in &quadrature.obstructions {
                retained.push((
                    route.named(),
                    obstruction.extension_index,
                    obstruction.winding_residual.clone(),
                ));
            }
        }
        retained
    }

    /// The reflection's law holds on this pair: the two faces lock exactly when the response is
    /// structurally causal.
    pub fn reflection_law_holds(&self) -> bool {
        self.lock.law_holds()
    }

    /// The pair is capable of deciding that law. A response supported only at the stimulus locks
    /// whatever it was, and a fixture built from one proves nothing.
    pub fn exercises_the_reflection(&self) -> bool {
        self.response.exercises_the_pairing()
    }

    /// The second route is the obstruction to extending the transfer polynomial over infinity.
    ///
    /// Exactly: the pair reads as structurally causal — the polynomial is holomorphic at infinity —
    /// if and only if the right route accumulated nothing anywhere. A pair that reads causal is a
    /// pair that was never two routes.
    pub fn second_route_is_the_obstruction(&self) -> bool {
        let right_is_silent = self
            .disagreement
            .right
            .steps
            .iter()
            .all(|step| step.increment.is_zero());
        self.holomorphy.extends_over_infinity() == right_is_silent
            && self.response.is_causal() == right_is_silent
    }

    /// The advanced indices where the response does not vanish: the second route, exhibited.
    pub fn advanced_witness(&self) -> Vec<(i64, Rat)> {
        self.response
            .advanced_support()
            .into_iter()
            .map(|index| (index, self.response.value(index)))
            .collect()
    }
}

/// Compare two routes with common endpoints and return every carrier's reading of their residual.
pub fn compare_routes(
    circuit: &ConditionedCircuit,
    cochain: &Cochain,
    rule: AccumulationRule,
    left: &Route,
    right: &Route,
) -> Result<RouteDisagreement, DerivationIntegralError> {
    let complex = circuit.circuit.complex();
    let compared = disagreement(complex, cochain, &left.path, &right.path)?;
    let left_integral = running_sum(complex, cochain, &left.path)?;
    let right_integral = running_sum(complex, cochain, &right.path)?;

    let left_material = route_material(&left_integral)?;
    let right_material = route_material(&right_integral)?;
    // Each route's own material declares its law. The two agree on this module's material because
    // both carry unit germs of rank-one jets; they are read separately so that they do not have to.
    let leader_left = integrate_by_leaders(&left_material, &leader_law(&left_material))?;
    let leader_right = integrate_by_leaders(&right_material, &leader_law(&right_material))?;
    let oracle_left = germwise_oracle_area(&left_material);
    let oracle_right = germwise_oracle_area(&right_material);
    let leader_residual = path_disagreement(&leader_left, &leader_right);

    let response = pair_response(&left_integral, &right_integral)?;
    let lock = causality_lock(&response)?;
    let holomorphy = response.holomorphy_witness();
    let reflected_residual = residual_from_reflection(&response);

    Ok(RouteDisagreement {
        schema: "holonic-engine.derivation-route-disagreement.v1".to_owned(),
        rule,
        left: left.clone(),
        right: right.clone(),
        left_founding: provenance(circuit, &compared.left),
        right_founding: provenance(circuit, &compared.right),
        disagreement: compared,
        leader_left,
        leader_right,
        oracle_left,
        oracle_right,
        leader_residual,
        response,
        lock,
        holomorphy,
        reflected_residual,
    })
}

// -------------------------------------------------------------------------------------------------
// the populations
// -------------------------------------------------------------------------------------------------

/// Every compared pair of one declared family, with what each returned.
#[derive(Clone, Debug)]
pub struct HolonomyPopulation {
    pub schema: String,
    /// What this family is, in words. Printed with the population; never an ordinal.
    pub family: String,
    pub rule: AccumulationRule,
    pub compared: Vec<RouteDisagreement>,
}

impl HolonomyPopulation {
    /// The pairs whose residual stands: the holonomy.
    pub fn standing(&self) -> Vec<&RouteDisagreement> {
        self.compared
            .iter()
            .filter(|pair| pair.stands())
            .collect()
    }

    /// The pairs whose two routes returned the same sum.
    pub fn agreeing(&self) -> Vec<&RouteDisagreement> {
        self.compared
            .iter()
            .filter(|pair| !pair.stands())
            .collect()
    }

    /// The residual values this family carries, each with every pair that returned it, named.
    pub fn residual_classes(&self) -> BTreeMap<BigInt, Vec<String>> {
        let mut classes: BTreeMap<BigInt, Vec<String>> = BTreeMap::new();
        for pair in &self.compared {
            classes
                .entry(pair.residual().clone())
                .or_default()
                .push(pair.named());
        }
        classes
    }

    pub fn is_empty(&self) -> bool {
        self.compared.is_empty()
    }

    pub fn winds(&self) -> bool {
        self.compared.iter().any(RouteDisagreement::stands)
    }

    pub fn every_pair_is_distinct(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::routes_are_distinct)
    }

    pub fn every_reading_agrees(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::three_readings_agree)
    }

    pub fn every_leader_is_graded(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::leader_grades_the_running_sum)
    }

    pub fn every_leader_founds_and_rides(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::leader_founds_and_rides)
    }

    pub fn every_reflection_law_holds(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::reflection_law_holds)
    }

    pub fn every_pair_exercises_the_reflection(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::exercises_the_reflection)
    }

    pub fn every_second_route_is_the_obstruction(&self) -> bool {
        self.compared
            .iter()
            .all(RouteDisagreement::second_route_is_the_obstruction)
    }
}

/// **The statement lineage, traversed.** Walk the declarations that reached one statement in
/// canonical order and, at every adjacent pair, compare the route that crosses the *result* against
/// every route that crosses an identifier both declarations recruit.
///
/// An integral wants a path, and this is the path through a statement's whole route lineage: every
/// declaration that reached it lies on the traversal exactly once, so no declaration is privileged
/// and no pair is selected for what it returns. A family that departed from one fixed declaration
/// would be an arbitrary frame — and worse, on real material it can be a *load outlier*, in which
/// case every comparison stands and the agreeing class is unreachable. The traversal is what makes
/// both classes available.
///
/// Under [`AccumulationRule::RouteLoad`] this family agrees identically and the agreement is
/// *forced*: both routes are head-determined and both return `Λ(to) - Λ(from)` whatever the material
/// says. That is a tautology, it is recorded here so it is never read as evidence, and the family
/// carries evidence only under [`AccumulationRule::RecruitmentLoad`], where the two routes read
/// disjoint parts of the multiset and can disagree.
pub fn statement_lineage(
    circuit: &ConditionedCircuit,
    cochain: &Cochain,
    rule: AccumulationRule,
    statement: &str,
) -> Result<HolonomyPopulation, DerivationIntegralError> {
    let loads = circuit_loads(circuit);
    let reaching: Vec<String> = declarations_reaching(circuit, statement)
        .into_iter()
        .collect();
    if reaching.len() < 2 {
        return Err(DerivationIntegralError::StatementCarriesNoPlurality {
            statement: statement.to_owned(),
            reaching: reaching.len(),
        });
    }
    let mut compared = Vec::new();
    for pair in reaching.windows(2) {
        let (from, to) = (&pair[0], &pair[1]);
        let Some(left) = route_via_statement(circuit, from, to, statement) else {
            continue;
        };
        for identifier in shared_recruitments(&loads, from, to) {
            let Some(right) = route_via_recruitment(circuit, from, to, &identifier) else {
                continue;
            };
            compared.push(compare_routes(circuit, cochain, rule, &left, &right)?);
        }
    }
    Ok(HolonomyPopulation {
        schema: "holonic-engine.derivation-holonomy-population.v1".to_owned(),
        family: format!(
            "the route lineage of |- {statement}, traversed in canonical order: at each adjacent \
             pair, crossing the result against crossing a shared identifier"
        ),
        rule,
        compared,
    })
}

/// **The recruited-declaration family.** For every declaration that some other declaration
/// recruited, compare the one-step route into it against every route that crosses an identifier both
/// recruit.
///
/// Empty exactly when no declaration is a resource — which is the head-separated case, where
/// [`AccumulationRule::RouteLoad`] admits a potential. On this family under `RouteLoad` the residual
/// is exactly `-Λ(to)`: the load of the derivation that is being used as a resource.
pub fn recruited_declaration_family(
    circuit: &ConditionedCircuit,
    cochain: &Cochain,
    rule: AccumulationRule,
) -> Result<HolonomyPopulation, DerivationIntegralError> {
    let loads = circuit_loads(circuit);
    let recruited = recruited_declarations(circuit);
    let mut compared = Vec::new();
    for to in &recruited {
        for from in loads.declarations() {
            if from == to.as_str() {
                continue;
            }
            let Some(left) = route_direct(circuit, from, to) else {
                continue;
            };
            for identifier in shared_recruitments(&loads, from, to) {
                let Some(right) = route_via_recruitment(circuit, from, to, &identifier) else {
                    continue;
                };
                compared.push(compare_routes(circuit, cochain, rule, &left, &right)?);
            }
        }
    }
    Ok(HolonomyPopulation {
        schema: "holonic-engine.derivation-holonomy-population.v1".to_owned(),
        family: "the recruited-declaration family: reaching a derivation as a resource against \
                 reaching it across a shared identifier"
            .to_owned(),
        rule,
        compared,
    })
}

// -------------------------------------------------------------------------------------------------
// the potential and its certified remainder
// -------------------------------------------------------------------------------------------------

/// One chord the tree's potential could not carry, named.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedChord {
    pub cell: String,
    pub tail: String,
    pub head: String,
    pub declared: BigInt,
    pub implied: BigInt,
    pub residual: BigInt,
    pub founding_passages: Vec<String>,
}

/// The search for a potential over one circuit, with its retained remainder named.
#[derive(Clone, Debug)]
pub struct NamedPotential {
    pub schema: String,
    pub rule: AccumulationRule,
    pub base: String,
    pub search: PotentialSearch,
    /// Every retained chord obstruction, with the cell and the passages that founded it.
    pub retained: Vec<NamedChord>,
}

impl NamedPotential {
    /// The cochain is a coboundary over the reached component: nothing was retained.
    pub fn admits_a_potential(&self) -> bool {
        self.search.admits_a_potential()
    }

    /// How many chords the search actually tested. A zero here would make an empty remainder
    /// vacuous — the walk found a tree and had nothing to test.
    pub fn cycle_rank(&self) -> usize {
        self.search.cycle_rank()
    }

    /// The distinct residual values retained, each with the cells that carry it.
    pub fn residual_classes(&self) -> BTreeMap<BigInt, Vec<String>> {
        let mut classes: BTreeMap<BigInt, Vec<String>> = BTreeMap::new();
        for chord in &self.retained {
            classes
                .entry(chord.residual.clone())
                .or_default()
                .push(chord.cell.clone());
        }
        classes
    }
}

/// Walk a spanning tree of the whole 1-skeleton from a named vertex, assign the only potential it
/// admits, and test every chord.
pub fn potential_over(
    circuit: &ConditionedCircuit,
    cochain: &Cochain,
    rule: AccumulationRule,
    base: &str,
) -> Result<NamedPotential, DerivationIntegralError> {
    let vertex = *circuit.circuit.vertices().get(base).ok_or_else(|| {
        DerivationIntegralError::NoSuchVertex {
            name: base.to_owned(),
        }
    })?;
    let search = found_potential(circuit.circuit.complex(), cochain, vertex)?;
    let retained = search
        .retained_obstructions
        .iter()
        .map(|chord| NamedChord {
            cell: cell_name(circuit, chord.cell),
            tail: cell_name(circuit, chord.tail),
            head: cell_name(circuit, chord.head),
            declared: chord.declared.clone(),
            implied: chord.implied.clone(),
            residual: chord.residual.clone(),
            founding_passages: circuit
                .passages_founding(chord.cell)
                .into_iter()
                .map(passage_label)
                .collect(),
        })
        .collect();
    Ok(NamedPotential {
        schema: "holonic-engine.derivation-integral-potential.v1".to_owned(),
        rule,
        base: base.to_owned(),
        search,
        retained,
    })
}

// -------------------------------------------------------------------------------------------------
// refusals
// -------------------------------------------------------------------------------------------------

#[derive(Debug, Error)]
pub enum DerivationIntegralError {
    #[error(transparent)]
    Integral(#[from] RunningIntegralError),
    #[error(transparent)]
    Leader(#[from] LeaderError),
    #[error(transparent)]
    Reflection(#[from] CausalReflectionError),
    #[error("the circuit carries no zero-cell named `{name}`")]
    NoSuchVertex { name: String },
    #[error(
        "`{statement}` was reached by {reaching} declaration(s); a lineage with no plurality \
         carries no pair of routes to compare"
    )]
    StatementCarriesNoPlurality { statement: String, reaching: usize },
}

// -------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use crate::conditioned_derivation::ConditionedBody;
    use crate::derivation_atlas::CircuitAperture;

    const STATEMENT: &str = "(P : Prop) : exactCarrier P";

    fn artifact(name: &str, body: &str) -> (String, String) {
        (
            format!("fixture/{name}.lean"),
            format!("namespace Soma\ntheorem {name} (P : Prop) : exactCarrier P := by\n{body}end Soma\n"),
        )
    }

    /// Three declarations, none of which is recruited by another. Head-separated.
    fn head_separated() -> Vec<(String, String)> {
        vec![
            artifact("alpha", "  have bridged := helper\n"),
            artifact("beta", "  have bridged := other\n"),
            artifact("gamma", "  have bridged := helper\n  have again := other\n"),
        ]
    }

    /// The same, plus one declaration that recruits `alpha` — `alpha` is now a result and a
    /// resource — and one that names `helper` **twice**, so the recruitment multiset carries a count
    /// above one and the grade against the complex's own boundary coefficients is not vacuous.
    fn with_a_recruited_declaration() -> Vec<(String, String)> {
        let mut deposit = head_separated();
        deposit.push(artifact("delta", "  have bridged := alpha\n"));
        deposit.push(artifact(
            "epsilon",
            "  have bridged := helper\n  have again := helper\n",
        ));
        deposit
    }

    fn circuit(deposit: Vec<(String, String)>) -> ConditionedCircuit {
        let body = ConditionedBody::mount(deposit).expect("the fixture declares theorems");
        found_conditioned_circuit(
            body.standing().to_vec(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("the fixture founds")
    }

    fn multiplicity_circuit(deposit: Vec<(String, String)>) -> ConditionedCircuit {
        let body = ConditionedBody::mount(deposit).expect("the fixture declares theorems");
        found_conditioned_circuit(
            body.standing().to_vec(),
            CircuitAperture::PER_ROUTE_MULTIPLICITY,
        )
        .expect("the fixture founds")
    }

    fn first_vertex(circuit: &ConditionedCircuit) -> String {
        circuit
            .circuit
            .vertices()
            .keys()
            .next()
            .cloned()
            .expect("the circuit founds vertices")
    }

    // --- the material itself ------------------------------------------------------------------

    #[test]
    fn the_fixture_reads_the_loads_the_artifacts_declare() {
        let loads = circuit_loads(&circuit(head_separated()));
        // `P` is a single-character binder the reader drops; `by` and `namespace` are codec
        // vocabulary; `theorem` founds the name after it. `Soma` is none of those, so the namespace
        // opener is a recruitment and the load carries it.
        assert_eq!(loads.recruitment_load("alpha", "Soma"), BigInt::from(1));
        assert_eq!(loads.recruitment_load("alpha", "Prop"), BigInt::from(1));
        assert_eq!(loads.recruitment_load("alpha", "exactCarrier"), BigInt::from(1));
        assert_eq!(loads.recruitment_load("alpha", "helper"), BigInt::from(1));
        assert_eq!(loads.recruitment_load("alpha", "other"), BigInt::zero());
        assert_eq!(loads.route_load("alpha"), BigInt::from(4));
        assert_eq!(loads.route_load("gamma"), BigInt::from(5));
    }

    #[test]
    fn loads_match_the_complexs_own_boundary_coefficients() {
        let founded = multiplicity_circuit(with_a_recruited_declaration());
        let loads = circuit_loads(&founded);
        // A grade in which every multiplicity is one cannot distinguish a summed multiset from a
        // set, and would be present in the code and absent from the evidence.
        assert!(
            loads
                .recruitment
                .values()
                .flat_map(BTreeMap::values)
                .any(|count| *count > BigInt::one()),
            "the fixture must carry a recruitment named more than once"
        );
        assert_eq!(loads_agree_with_the_boundary(&founded), Some(true));
    }

    #[test]
    fn an_incidence_aperture_cannot_grade_the_load_table_and_says_so() {
        assert_eq!(
            loads_agree_with_the_boundary(&circuit(head_separated())),
            None
        );
    }

    #[test]
    fn only_a_declaration_that_is_also_recruited_is_returned() {
        assert!(recruited_declarations(&circuit(head_separated())).is_empty());
        assert_eq!(
            recruited_declarations(&circuit(with_a_recruited_declaration())),
            BTreeSet::from(["alpha".to_owned()])
        );
    }

    // --- the routes ---------------------------------------------------------------------------

    #[test]
    fn route_via_recruitment_joins_from_declaration_to_declaration() {
        let founded = circuit(head_separated());
        let route = route_via_recruitment(&founded, "alpha", "beta", "Prop").expect("shared");
        let (start, end) = route
            .path
            .endpoints(founded.circuit.complex())
            .expect("the route joins");
        assert_eq!(start, founded.circuit.vertices()["alpha"]);
        assert_eq!(end, founded.circuit.vertices()["beta"]);
    }

    #[test]
    fn route_via_statement_joins_from_declaration_to_declaration() {
        let founded = circuit(head_separated());
        let route = route_via_statement(&founded, "alpha", "beta", STATEMENT).expect("both reach");
        let (start, end) = route
            .path
            .endpoints(founded.circuit.complex())
            .expect("the route joins");
        assert_eq!(start, founded.circuit.vertices()["alpha"]);
        assert_eq!(end, founded.circuit.vertices()["beta"]);
    }

    #[test]
    fn a_direct_route_exists_exactly_where_a_declaration_was_recruited() {
        let separated = circuit(head_separated());
        assert!(route_direct(&separated, "beta", "alpha").is_none());
        let collided = circuit(with_a_recruited_declaration());
        let route = route_direct(&collided, "delta", "alpha").expect("delta recruits alpha");
        assert_eq!(route.path.len(), 1);
        let (start, end) = route
            .path
            .endpoints(collided.circuit.complex())
            .expect("the route joins");
        assert_eq!(start, collided.circuit.vertices()["delta"]);
        assert_eq!(end, collided.circuit.vertices()["alpha"]);
    }

    // --- the two rules ------------------------------------------------------------------------

    #[test]
    fn route_load_is_head_determined_and_recruitment_load_is_not() {
        let founded = circuit(head_separated());
        let by_route = accumulation(&founded, AccumulationRule::RouteLoad);
        let by_recruitment = accumulation(&founded, AccumulationRule::RecruitmentLoad);
        let cell = founded.circuit.recruitments()[&("gamma".to_owned(), "Prop".to_owned())];
        assert_eq!(by_route.value(cell), BigInt::from(5));
        assert_eq!(by_recruitment.value(cell), BigInt::from(1));
        assert_ne!(by_route, by_recruitment);
    }

    #[test]
    fn route_load_admits_a_potential_when_no_declaration_is_recruited() {
        let founded = circuit(head_separated());
        let cochain = accumulation(&founded, AccumulationRule::RouteLoad);
        let base = first_vertex(&founded);
        let potential =
            potential_over(&founded, &cochain, AccumulationRule::RouteLoad, &base).expect("walks");
        assert!(potential.admits_a_potential(), "{:?}", potential.retained);
        assert!(
            potential.cycle_rank() > 0,
            "an empty remainder over no chords tests nothing"
        );
    }

    #[test]
    fn route_load_winds_exactly_at_the_recruited_declaration() {
        let founded = circuit(with_a_recruited_declaration());
        let cochain = accumulation(&founded, AccumulationRule::RouteLoad);
        let base = first_vertex(&founded);
        let potential =
            potential_over(&founded, &cochain, AccumulationRule::RouteLoad, &base).expect("walks");
        assert!(!potential.admits_a_potential());
        assert!(potential
            .retained
            .iter()
            .all(|chord| chord.tail == "alpha" || chord.head == "alpha"));
        assert!(potential
            .retained
            .iter()
            .all(|chord| !chord.founding_passages.is_empty()));
    }

    #[test]
    fn removing_the_declaring_artifacts_returns_the_potential() {
        let founded = circuit(with_a_recruited_declaration());
        let ablated =
            without_declarations(&founded, &BTreeSet::from(["alpha".to_owned()])).expect("founds");
        assert!(recruited_declarations(&ablated).is_empty());
        let cochain = accumulation(&ablated, AccumulationRule::RouteLoad);
        let base = first_vertex(&ablated);
        let potential =
            potential_over(&ablated, &cochain, AccumulationRule::RouteLoad, &base).expect("walks");
        assert!(potential.admits_a_potential(), "{:?}", potential.retained);
        assert!(potential.cycle_rank() > 0);
    }

    #[test]
    fn recruitment_load_winds_on_both_circuits() {
        for deposit in [head_separated(), with_a_recruited_declaration()] {
            let founded = circuit(deposit);
            let cochain = accumulation(&founded, AccumulationRule::RecruitmentLoad);
            let base = first_vertex(&founded);
            let potential =
                potential_over(&founded, &cochain, AccumulationRule::RecruitmentLoad, &base)
                    .expect("walks");
            assert!(!potential.admits_a_potential());
        }
    }

    #[test]
    fn the_ablation_keeps_provenance_total_and_re_indexes_its_passages() {
        let founded = circuit(with_a_recruited_declaration());
        let ablated =
            without_declarations(&founded, &BTreeSet::from(["alpha".to_owned()])).expect("founds");
        assert!(ablated.provenance_is_total(), "{:?}", ablated.unclaimed);
        for (ordinal, passage) in ablated.passages.iter().enumerate() {
            assert_eq!(passage.id, PassageId(ordinal as u64));
        }
        for cell in ablated.circuit.complex().cells().values() {
            for passage in ablated.passages_founding(cell.id) {
                let named = ablated
                    .circuit
                    .vertices()
                    .contains_key(&passage.derivation.name)
                    || !passage.derivation.recruited.is_empty();
                assert!(named, "a founding passage must belong to this circuit");
            }
        }
    }

    // --- the compared pair --------------------------------------------------------------------

    fn winding_pair() -> RouteDisagreement {
        let founded = circuit(with_a_recruited_declaration());
        let cochain = accumulation(&founded, AccumulationRule::RouteLoad);
        let left = route_direct(&founded, "delta", "alpha").expect("direct");
        let right = route_via_recruitment(&founded, "delta", "alpha", "Prop").expect("shared");
        compare_routes(
            &founded,
            &cochain,
            AccumulationRule::RouteLoad,
            &left,
            &right,
        )
        .expect("compares")
    }

    #[test]
    fn the_holonomy_at_a_recruited_declaration_is_its_own_load() {
        let pair = winding_pair();
        let founded = circuit(with_a_recruited_declaration());
        let loads = circuit_loads(&founded);
        assert!(pair.stands());
        assert_eq!(*pair.residual(), -loads.route_load("alpha"));
    }

    #[test]
    fn a_compared_pair_names_the_passages_that_founded_every_cell_it_crossed() {
        let pair = winding_pair();
        assert!(!pair.left_founding.is_empty());
        assert!(pair
            .left_founding
            .iter()
            .chain(&pair.right_founding)
            .all(|carried| !carried.passages.is_empty()));
        assert!(pair
            .left_founding
            .iter()
            .any(|carried| carried.passages.iter().any(|name| name.contains("delta"))));
    }

    #[test]
    fn three_readings_of_one_holonomy_agree() {
        let pair = winding_pair();
        assert!(pair.three_readings_agree());
        assert_eq!(pair.leader_residual, rational(pair.residual()));
        assert_eq!(pair.reflected_residual, rational(pair.residual()));
    }

    #[test]
    fn the_leader_grades_every_route_against_its_germwise_antiderivative() {
        let pair = winding_pair();
        assert!(pair.leader_grades_the_running_sum());
    }

    #[test]
    fn every_route_material_both_founds_and_rides() {
        let pair = winding_pair();
        assert!(pair.leader_founds_and_rides());
        assert_eq!(pair.leader_left.found_count(), pair.leader_left.ride_count());
        assert!(!pair.leader_left.scale_witnesses.is_empty());
    }

    #[test]
    fn the_second_route_is_the_advanced_half_and_the_obstruction_at_infinity() {
        let pair = winding_pair();
        assert!(!pair.response.is_causal());
        assert!(!pair.holomorphy.extends_over_infinity());
        assert!(pair.second_route_is_the_obstruction());
        let witness = pair.advanced_witness();
        assert_eq!(witness.len(), pair.right.path.len());
        assert!(pair.exercises_the_reflection());
        assert!(pair.reflection_law_holds());
    }

    #[test]
    fn the_reflection_recovers_the_residual_from_the_odd_face_alone() {
        let pair = winding_pair();
        assert!(pair.response.instantaneous_value().is_zero());
        assert_eq!(residual_from_reflection(&pair.response), pair.leader_residual);
    }

    #[test]
    fn a_pair_of_routes_that_are_the_same_chain_is_refused_as_evidence() {
        let founded = circuit(head_separated());
        let cochain = accumulation(&founded, AccumulationRule::RecruitmentLoad);
        let route = route_via_recruitment(&founded, "alpha", "beta", "Prop").expect("shared");
        let pair = compare_routes(
            &founded,
            &cochain,
            AccumulationRule::RecruitmentLoad,
            &route,
            &route,
        )
        .expect("compares");
        assert!(!pair.stands());
        assert!(
            !pair.routes_are_distinct(),
            "a pair whose cycle is zero must report itself indistinct"
        );
    }

    // --- the populations ----------------------------------------------------------------------

    #[test]
    fn a_population_separates_standing_from_agreeing_and_names_both() {
        let founded = circuit(with_a_recruited_declaration());
        let cochain = accumulation(&founded, AccumulationRule::RecruitmentLoad);
        let population =
            statement_lineage(&founded, &cochain, AccumulationRule::RecruitmentLoad, STATEMENT)
                .expect("traverses");
        assert!(!population.is_empty());
        assert!(population.every_pair_is_distinct());
        assert!(population.winds(), "{:?}", population.residual_classes());
        assert!(!population.agreeing().is_empty());
        assert_eq!(
            population.standing().len() + population.agreeing().len(),
            population.compared.len()
        );
        for pair in &population.compared {
            assert!(!pair.named().is_empty());
        }
    }

    #[test]
    fn the_statement_lineage_agrees_by_force_under_the_head_determined_rule() {
        let founded = circuit(with_a_recruited_declaration());
        let cochain = accumulation(&founded, AccumulationRule::RouteLoad);
        let population =
            statement_lineage(&founded, &cochain, AccumulationRule::RouteLoad, STATEMENT)
                .expect("traverses");
        assert!(!population.is_empty());
        assert!(population.every_pair_is_distinct());
        assert!(
            !population.winds(),
            "a head-determined rule cannot wind on two head-determined routes"
        );
    }

    #[test]
    fn the_recruited_declaration_family_is_empty_exactly_when_no_declaration_is_a_resource() {
        let separated = circuit(head_separated());
        let separated_cochain = accumulation(&separated, AccumulationRule::RouteLoad);
        assert!(recruited_declaration_family(
            &separated,
            &separated_cochain,
            AccumulationRule::RouteLoad
        )
        .expect("family")
        .is_empty());

        let collided = circuit(with_a_recruited_declaration());
        let collided_cochain = accumulation(&collided, AccumulationRule::RouteLoad);
        let population =
            recruited_declaration_family(&collided, &collided_cochain, AccumulationRule::RouteLoad)
                .expect("family");
        assert!(!population.is_empty());
        assert!(population.winds());
        assert!(population.every_pair_is_distinct());
        assert!(population.every_reading_agrees());
        assert!(population.every_leader_is_graded());
        assert!(population.every_leader_founds_and_rides());
        assert!(population.every_reflection_law_holds());
        assert!(population.every_pair_exercises_the_reflection());
        assert!(population.every_second_route_is_the_obstruction());
    }

    #[test]
    fn the_residual_classes_name_their_pairs_rather_than_counting_them() {
        let founded = circuit(with_a_recruited_declaration());
        let cochain = accumulation(&founded, AccumulationRule::RouteLoad);
        let population =
            recruited_declaration_family(&founded, &cochain, AccumulationRule::RouteLoad)
                .expect("family");
        let classes = population.residual_classes();
        assert!(!classes.is_empty());
        for (residual, named) in &classes {
            assert!(!named.is_empty());
            assert!(named.iter().all(|entry| entry.contains("alpha")));
            assert_eq!(*residual, BigInt::from(-4));
        }
    }

    #[test]
    fn a_missing_vertex_and_a_lineage_with_no_plurality_are_refused_by_name() {
        let founded = circuit(head_separated());
        let cochain = accumulation(&founded, AccumulationRule::RouteLoad);
        assert!(matches!(
            potential_over(&founded, &cochain, AccumulationRule::RouteLoad, "nowhere"),
            Err(DerivationIntegralError::NoSuchVertex { .. })
        ));
        assert!(matches!(
            statement_lineage(&founded, &cochain, AccumulationRule::RouteLoad, "nowhere"),
            Err(DerivationIntegralError::StatementCarriesNoPlurality { reaching: 0, .. })
        ));
        // One artifact reaching a statement is a lineage with no plurality: there is no second
        // route, so there is no pair, and returning an empty population would read as agreement.
        let lonely = ConditionedBody::mount(vec![(
            "fixture/lonely.lean".to_owned(),
            "namespace Soma\ntheorem lonely (Q : Prop) : otherCarrier Q := by\n  have bridged := helper\nend Soma\n"
                .to_owned(),
        )])
        .expect("declares");
        let lonely_circuit = found_conditioned_circuit(
            lonely.standing().to_vec(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("founds");
        let lonely_cochain = accumulation(&lonely_circuit, AccumulationRule::RouteLoad);
        assert!(matches!(
            statement_lineage(
                &lonely_circuit,
                &lonely_cochain,
                AccumulationRule::RouteLoad,
                "(Q : Prop) : otherCarrier Q"
            ),
            Err(DerivationIntegralError::StatementCarriesNoPlurality { reaching: 1, .. })
        ));
    }

    // ---------------------------------------------------------------------------------------------
    // The conducted return
    // ---------------------------------------------------------------------------------------------

    /// Every 1-cell of the circuit, as one declared structure. The family is the caller's.
    fn whole_structure(circuit: &ConditionedCircuit) -> Vec<(String, BTreeSet<CausalCellId>)> {
        let complex = circuit.circuit.complex();
        let cells: BTreeSet<CausalCellId> = complex
            .cells()
            .values()
            .filter(|cell| cell.grade == 1)
            .map(|cell| cell.id)
            .collect();
        vec![("whole".to_owned(), cells)]
    }

    /// **The reading enters the next production as material, and something moves.**
    ///
    /// The falsifier `blueprint/THE_ROADMAP.md` names for the accumulation cut: *"Require
    /// `invariant_movement` to be non-zero and attributable — each moved invariant naming the
    /// earlier return that caused it. A second production bit-identical to the first has not closed
    /// the cycle, whatever it printed."*
    #[test]
    fn the_reading_returns_as_material_and_the_second_reading_moves() {
        let circuit = circuit(head_separated());
        let complex = circuit.circuit.complex();
        let base = complex
            .cells()
            .values()
            .find(|cell| cell.grade == 0)
            .map(|cell| cell.id)
            .expect("the fixture founds a vertex");
        let family = whole_structure(&circuit);
        let returned = conduct_return(&circuit, AccumulationRule::RecruitmentLoad, base, &family)
            .expect("the fixture reads");

        // The first reading must actually find an obstruction, or there is nothing to return and
        // the test would pass on a vacuum.
        assert!(
            !returned.deposits.is_empty(),
            "the first reading found no leak, so the return is vacuous: {:?}",
            returned.before
        );
        // And the second reading must differ from the first.
        assert!(
            returned.moved_at_all(),
            "the second reading was identical to the first.
  deposits {:?}
  before {:?}
  after {:?}",
            returned.deposits, returned.before, returned.after
        );
        // And every movement must name the deposit that caused it.
        assert!(
            returned.every_movement_is_attributable(),
            "unattributable movement: {:?}",
            returned.unattributable()
        );
    }

    /// **The control that keeps the test above honest.** An empty structure has no cycles, so it is
    /// `Closed`, so it deposits nothing — and the second reading must then be identical. A body that
    /// moves without a deposit did not move because of the return.
    #[test]
    fn a_closed_structure_deposits_nothing_and_the_second_reading_does_not_move() {
        let circuit = circuit(head_separated());
        let complex = circuit.circuit.complex();
        let base = complex
            .cells()
            .values()
            .find(|cell| cell.grade == 0)
            .map(|cell| cell.id)
            .expect("a vertex");
        let empty = vec![("empty".to_owned(), BTreeSet::new())];

        let returned = conduct_return(&circuit, AccumulationRule::RecruitmentLoad, base, &empty)
            .expect("the fixture reads");

        assert!(returned.deposits.is_empty(), "a closed structure returned something");
        assert!(!returned.moved_at_all(), "movement with no deposit: {:?}", returned.moved);
        assert_eq!(returned.before, returned.after);
    }
}

// -------------------------------------------------------------------------------------------------
// The conducted return: a reading enters the next production as material
// -------------------------------------------------------------------------------------------------

/// **What one structure's reading deposited, and what moved because of it.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedDeposit {
    /// The structure whose reading produced the value.
    pub from: String,
    /// The cell the caller declared it lands on.
    pub at: CausalCellId,
    /// The retained leak, deposited whole. Never a summary of it.
    pub value: BigInt,
}

/// **One conducted return.** The reading is taken, its obstruction is deposited into the shared
/// cochain, and the reading is taken again against the changed material.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConductedReturn {
    pub before: crate::temper::TemperedFamily,
    /// Every deposit made, each naming the structure whose reading produced it.
    pub deposits: Vec<ReturnedDeposit>,
    pub after: crate::temper::TemperedFamily,
    /// The structures whose twist changed, each paired with the deposits that could have caused it.
    pub moved: Vec<(String, Vec<String>)>,
}

impl ConductedReturn {
    /// **The cycle closed and something moved.** A second reading identical to the first has not
    /// closed anything, whatever it printed.
    pub fn moved_at_all(&self) -> bool {
        !self.moved.is_empty()
    }

    /// **Every movement names an earlier return.** This is the half that separates a conducted
    /// return from a coincidence: a structure that moved with no deposit attributable to it is a
    /// movement this organ cannot account for, and it is reported rather than counted.
    pub fn every_movement_is_attributable(&self) -> bool {
        !self.moved.is_empty() && self.moved.iter().all(|(_, causes)| !causes.is_empty())
    }

    pub fn unattributable(&self) -> Vec<&str> {
        self.moved
            .iter()
            .filter(|(_, causes)| causes.is_empty())
            .map(|(name, _)| name.as_str())
            .collect()
    }
}

/// **Conduct one return.**
///
/// `blueprint/THE_ROADMAP.md`'s accumulation cut names this exact pair: *"`temper` ⇄
/// `derivation_integral`, through `Cochain`, in **both** directions… **Neither file references the
/// other.**"* Both halves were built and nothing sat between them.
///
/// The loop, and every step is an existing organ:
///
/// ```text
///   accumulation(circuit, rule)          -> Cochain          the production's own 1-cochain
///   TemperedFamily::read(…, &cochain, …) -> the reading      which structures leak, and by how much
///   temper::found_on(&cochain, at, leak) -> Cochain          THE READING BECOMES MATERIAL
///   TemperedFamily::read(…, &founded, …) -> the next reading against the changed world
/// ```
///
/// **The return is world-mediated, not wired.** `canon/THE_HOLOBROCHOS_SPINE.md` §5b: *"A consequence
/// handed from a reading to a production across a call, without leaving the process and landing in
/// the world's own record, is the shape Soma's contaminant list names. **The consequence returns as a
/// PLACE.**"* Here the place is a cell of the shared cochain: the deposit is not passed to the second
/// read, it is written into the material the second read consults, and the second read does not know
/// where it came from.
///
/// **Only a retained obstruction is deposited, and the place is read off the material.** A
/// `Twist::Closed` structure has nothing to return — depositing on it would be inventing a residual.
/// A `Twist::Open` one carries `ChordObstruction`s, and each names **its own cell**, so the residual
/// returns exactly where the reading found it. There is no caller-declared deposit site and no
/// authored level: the reading says where its own residual lives.
///
/// **What the deposit does to the structure is the material's business, not this organ's.**
/// `temper::found_on` is the *opening* face — *"depositing a value on one cell that the potential
/// does not imply opens the structure"* — so returning the residual may open the structure further
/// rather than close it. Which happens is what the second reading measures, and this function
/// reports it either way rather than choosing a correction that would make the outcome its own.
pub fn conduct_return(
    circuit: &ConditionedCircuit,
    rule: AccumulationRule,
    base: CausalCellId,
    family: &[(String, BTreeSet<CausalCellId>)],
) -> Result<ConductedReturn, RunningIntegralError> {
    use crate::temper::{found_on, TemperedFamily, Twist};

    let complex = circuit.circuit.complex();
    let cochain = accumulation(circuit, rule);
    let before = TemperedFamily::read(complex, &cochain, base, family)?;

    let mut founded = cochain.clone();
    let mut deposits = Vec::new();
    for (name, twist) in &before.twists {
        let Twist::Open { obstructions, .. } = twist else { continue };
        for obstruction in obstructions {
            founded = found_on(&founded, obstruction.cell, obstruction.residual.clone());
            deposits.push(ReturnedDeposit {
                from: name.clone(),
                at: obstruction.cell,
                value: obstruction.residual.clone(),
            });
        }
    }

    let after = TemperedFamily::read(complex, &founded, base, family)?;

    // A structure moved when its twist differs. It is attributable to a deposit exactly when that
    // deposit's cell lies inside the structure the second read consulted — which is what makes the
    // attribution a fact about the incidence rather than about the order of the loop above.
    let structures: BTreeMap<&str, &BTreeSet<CausalCellId>> = family
        .iter()
        .map(|(name, cells)| (name.as_str(), cells))
        .collect();
    let mut moved = Vec::new();
    for ((name, was), (_, now)) in before.twists.iter().zip(after.twists.iter()) {
        if was == now {
            continue;
        }
        let causes: Vec<String> = deposits
            .iter()
            .filter(|deposit| {
                structures
                    .get(name.as_str())
                    .is_some_and(|cells| cells.contains(&deposit.at))
            })
            .map(|deposit| deposit.from.clone())
            .collect();
        moved.push((name.clone(), causes));
    }

    Ok(ConductedReturn {
        before,
        deposits,
        after,
        moved,
    })
}
