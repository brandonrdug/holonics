//! The constructive meaning of a name: the transitive closure of what it recruits, as a complex.
//!
//! ## Why this organ is owed
//!
//! The machine's reading of its own derivations was **orthographic**.
//! [`crate::conditioned_derivation`] founds a stem when a substring recurs across two distinct
//! wholes, and `exactCarrier -> exact|carrier` decomposes a *string*. Nothing in that path carries a
//! denotation, so `exactCarrier apply` is exactly as licensable as `exact_chart_carry P` and the
//! production returns both.
//!
//! In type theory the organ that supplies a denotation is **elaboration**: the constructive
//! production of the fully explicit term a surface expression stands for. A standing ruling in this
//! project bars Lean from being the judge — it is an export codec — so the machine needs its own,
//! and it already owns the carrier. [`crate::derivation_atlas`]'s 1-cells are **recruitments**:
//! *this derivation named that symbol*. So:
//!
//! > **The elaboration of a name is the transitive closure of what it recruits, as a complex.**
//!
//! Constructive, never a lookup. Nothing is consulted that the deposit does not already carry, and
//! the returned meaning of a name contains constituents the name does not name — reached only by
//! opening what it *does* name, and then what *that* names.
//!
//! ## What is retained that a reachability set would flatten
//!
//! ```text
//!   entered_at   the FIRST depth at which a constituent entered
//!   depths       EVERY depth at which it was reached -- a constituent reached directly and again
//!                through four steps is not the same as one reached only directly
//!   arrivals     the recruitment edges that brought it, each naming the constituent it came from
//!                and the depth of that passage
//! ```
//!
//! A depth is not a score. Nothing here ranks, gates, or discards on it; it is the length of the
//! shortest passage from the root, retained beside every other length at which the constituent was
//! reached, and [`Elaboration::signature`] hands both back.
//!
//! ## Cycles are retained as cycles
//!
//! A mutually recursive pair of declarations is a **real** cycle in the recruitment relation, and
//! truncating the walk at the second visit would report it as a depth rather than as what it is.
//! The walk therefore does not re-expand a constituent it has already opened — that is what makes it
//! terminate — but it **records the arrival anyway**, and [`Elaboration::cycles`] returns the
//! strongly connected components of the arrival digraph, each with a witness passage that returns to
//! its own start. A self-recruitment is a cycle of one member and is returned as one.
//!
//! **Declared difference from the circuit.** `derivation_atlas::found_circuit` drops a
//! self-recruitment (`if symbol == &derivation.name { continue }`), so a declaration that names
//! itself founds no 1-cell there. This organ keeps it, because a self-recruitment is exactly the
//! shape whose cycle a meaning has to carry. The two readings therefore disagree on such material by
//! construction, and that disagreement is stated here rather than discovered later.
//!
//! ## The aperture, and what lies outside it
//!
//! Two apertures are declared and both are returned with the reading:
//!
//! - **The deposit's own.** A recruited symbol the deposit does not declare cannot be opened: `Prop`,
//!   `assumption`, `rfl` and their siblings are supplied by an environment this reading does not
//!   hold. They are [`Elaboration::atoms`] — reached, named, and permanently outside. This is not a
//!   failure of the walk; it is the boundary of what the deposit means by itself.
//! - **A declared depth.** [`ElaborationAperture::ToDepth`] stops the walk, and what it stopped at is
//!   returned by name: [`Elaboration::beyond_depth`] is the openable constituents the walk did not
//!   open, and [`Elaboration::unopened`] is what opening them would have brought and the reading
//!   therefore does not carry. [`ElaborationAperture::Exhausted`] runs to closure and returns both
//!   empty, which is a report that the aperture was not the binding constraint.
//!
//! ## What a name resolves to
//!
//! A root and a constituent are both **keys**, and a key is either a route (`name#ordinal`, one
//! deposited artifact) or a declared name. The declared rule, stated once:
//!
//! ```text
//!   a route key       resolves to that one artifact's recruitment
//!   a declared name   resolves to the union of the recruitment of every artifact declaring it
//!   anything else     is an atom
//! ```
//!
//! The union is what the deposit collectively means by the name, and every arrival retains the
//! routes that supplied it ([`Arrival::routes`]), so the plurality is carried rather than summed
//! away. **The counts are lineage and never a boundary coefficient**: the elaboration complex is
//! founded under incidence coefficients only, because summing occurrence counts across the artifacts
//! of one declaration is precisely the merge `derivation_atlas::DerivationAtlasRefusal::
//! MultiplicityWouldSumRoutes` refuses, and this organ must not do by pooling what that one refuses
//! to do by aperture.
//!
//! ## No float, no scalar governor
//!
//! Depths and counts are `usize`/`u32` populations; the complex's coefficients are
//! `ComparativeMultiplicity` over `BigUint`. Nothing is compared by magnitude to select a return,
//! nothing is thresholded, and every constituent the walk reached is in the returned population
//! whatever its depth.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::causal::EventId;
use crate::derivation_atlas::Derivation;

/// The separator between a declaration name and its ordinal in a route key. `derivation_atlas`
/// writes `format!("{}#{ordinal}", derivation.name)` and a Lean identifier cannot carry `#`, so the
/// two key species can never collide.
pub const ROUTE_KEY_SEPARATOR: char = '#';

/// How far the walk is permitted to open what it reaches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ElaborationAperture {
    /// Open everything openable until nothing new is reached.
    Exhausted,
    /// Open nothing past this depth. Depth zero opens nothing at all and returns the root alone.
    ToDepth(usize),
}

impl ElaborationAperture {
    /// Whether a constituent standing at `depth` may be opened.
    pub const fn may_open(&self, depth: usize) -> bool {
        match self {
            Self::Exhausted => true,
            Self::ToDepth(limit) => depth < *limit,
        }
    }
}

/// One recruitment passage that brought a constituent into a meaning.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Arrival {
    /// The constituent whose own recruitment carried this one.
    pub from: String,
    /// The constituent it carried.
    pub to: String,
    /// The depth `to` stands at across this passage: one past the depth of `from`.
    pub at_depth: usize,
    /// How many times the source named it, summed over the routes that supplied it. Lineage; never
    /// a boundary coefficient. See the module documentation.
    pub occurrences: u32,
    /// The deposited routes whose recruitment carried this passage, keyed `name#ordinal`.
    pub routes: Vec<String>,
}

/// One constituent of a meaning, with every depth at which the walk reached it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constituent {
    pub name: String,
    /// The shortest passage from the root, in recruitment steps. The root itself stands at zero.
    pub entered_at: usize,
    /// Every depth at which the walk reached it. Never reduced to its minimum.
    pub depths: BTreeSet<usize>,
    /// The deposit declares this name, so the walk could open it.
    pub declared: bool,
    /// The walk did open it. False for an atom, and false for a constituent the depth aperture
    /// stopped at.
    pub opened: bool,
}

/// A cycle in the recruitment relation, returned whole.
///
/// `members` is a strongly connected component of the arrival digraph carrying more than one
/// constituent, or a single constituent that recruits itself. `witness` is one passage that leaves
/// the first member and returns to it, so the cycle is exhibited as a cycle and not as a set.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RetainedCycle {
    pub members: Vec<String>,
    pub witness: Vec<String>,
}

impl RetainedCycle {
    /// A single constituent that recruits itself.
    pub fn is_self_recruitment(&self) -> bool {
        self.members.len() == 1
    }
}

/// The constructive meaning of one name under one deposit and one declared aperture.
#[derive(Clone, Debug)]
pub struct Elaboration {
    root: String,
    aperture: ElaborationAperture,
    constituents: BTreeMap<String, Constituent>,
    arrivals: Vec<Arrival>,
    cycles: Vec<RetainedCycle>,
    atoms: BTreeSet<String>,
    beyond_depth: BTreeSet<String>,
    unopened: BTreeSet<String>,
    complex: GradedCausalComplex,
    vertices: BTreeMap<String, CausalCellId>,
    edges: BTreeMap<(String, String), CausalCellId>,
}

impl Elaboration {
    pub fn root(&self) -> &str {
        &self.root
    }

    pub const fn aperture(&self) -> ElaborationAperture {
        self.aperture
    }

    /// Every constituent, the root included, keyed by name.
    pub const fn constituents(&self) -> &BTreeMap<String, Constituent> {
        &self.constituents
    }

    /// Every recruitment passage the walk took, in walk order.
    pub fn arrivals(&self) -> &[Arrival] {
        &self.arrivals
    }

    /// The cycles the recruitment relation carries inside this meaning. Retained, never truncated.
    pub fn cycles(&self) -> &[RetainedCycle] {
        &self.cycles
    }

    /// Constituents the deposit does not declare. The environment's own vocabulary, and the
    /// permanent outside of this reading's aperture.
    pub const fn atoms(&self) -> &BTreeSet<String> {
        &self.atoms
    }

    /// Openable constituents the depth aperture stopped the walk at. Empty at
    /// [`ElaborationAperture::Exhausted`].
    pub const fn beyond_depth(&self) -> &BTreeSet<String> {
        &self.beyond_depth
    }

    /// What opening [`Self::beyond_depth`] would have brought and this reading does not carry.
    /// Exhibited by name, which is what makes the aperture auditable rather than asserted.
    pub const fn unopened(&self) -> &BTreeSet<String> {
        &self.unopened
    }

    /// The meaning as a complex: one 0-cell per constituent, one 1-cell per recruitment passage.
    pub const fn complex(&self) -> &GradedCausalComplex {
        &self.complex
    }

    pub const fn vertices(&self) -> &BTreeMap<String, CausalCellId> {
        &self.vertices
    }

    pub const fn edges(&self) -> &BTreeMap<(String, String), CausalCellId> {
        &self.edges
    }

    /// Constituent to the first depth at which it entered. What two meanings are compared on.
    pub fn signature(&self) -> BTreeMap<&str, usize> {
        self.constituents
            .values()
            .map(|carried| (carried.name.as_str(), carried.entered_at))
            .collect()
    }

    /// Every constituent that entered at exactly this depth.
    pub fn at_depth(&self, depth: usize) -> BTreeSet<&str> {
        self.constituents
            .values()
            .filter(|carried| carried.entered_at == depth)
            .map(|carried| carried.name.as_str())
            .collect()
    }

    /// The greatest depth any constituent entered at.
    pub fn reach(&self) -> usize {
        self.constituents
            .values()
            .map(|carried| carried.entered_at)
            .max()
            .unwrap_or(0)
    }

    /// **What the meaning was built out of rather than looked up in.** Every constituent the root's
    /// own recruitment does not carry — reached only by opening something the root *does* name.
    ///
    /// This is the population that makes the organ constructive: it is empty exactly when the
    /// closure added nothing to the direct recruitment, and a reading whose returns all live here at
    /// depth one has done a lookup.
    pub fn constructed(&self) -> BTreeSet<&str> {
        self.constituents
            .values()
            .filter(|carried| carried.entered_at >= 2)
            .map(|carried| carried.name.as_str())
            .collect()
    }

    /// One shortest passage from the root to a constituent, as the names it crosses.
    ///
    /// Returns `None` when the constituent is not in the meaning. For the root it returns the root
    /// alone.
    pub fn construction_path(&self, to: &str) -> Option<Vec<String>> {
        if !self.constituents.contains_key(to) {
            return None;
        }
        if to == self.root {
            return Some(vec![self.root.clone()]);
        }
        // Walk back along an arrival whose `from` stands one depth shallower. Every constituent
        // except the root has at least one such arrival, because `entered_at` is the depth of the
        // arrival that first reached it.
        let mut path = vec![to.to_owned()];
        let mut here = to.to_owned();
        loop {
            let depth = self.constituents.get(&here)?.entered_at;
            if depth == 0 {
                break;
            }
            let step = self.arrivals.iter().find(|arrival| {
                arrival.to == here
                    && arrival.at_depth == depth
                    && self
                        .constituents
                        .get(&arrival.from)
                        .is_some_and(|from| from.entered_at + 1 == depth)
            })?;
            here = step.from.clone();
            path.push(here.clone());
        }
        path.reverse();
        Some(path)
    }
}

/// A deposited derivation population, indexed so a key resolves to what it recruits.
#[derive(Clone, Debug, Default)]
pub struct ElaborationDeposit {
    routes: Vec<Derivation>,
    route_keys: Vec<String>,
    route_index: BTreeMap<String, usize>,
    declarations: BTreeMap<String, Vec<usize>>,
    pooled: BTreeMap<String, BTreeMap<String, u32>>,
}

impl ElaborationDeposit {
    /// Index a population in its own read order. The route keys are `name#ordinal` over that order,
    /// which is byte-identical to what `derivation_atlas::DerivationIdentity::ByRoute` founds, so an
    /// elaboration root and a circuit 0-cell are the same string.
    pub fn read(routes: &[Derivation]) -> Self {
        let mut deposit = Self {
            routes: routes.to_vec(),
            ..Self::default()
        };
        for (ordinal, derivation) in routes.iter().enumerate() {
            let key = format!("{}{ROUTE_KEY_SEPARATOR}{ordinal}", derivation.name);
            deposit.route_index.insert(key.clone(), ordinal);
            deposit.route_keys.push(key);
            deposit
                .declarations
                .entry(derivation.name.clone())
                .or_default()
                .push(ordinal);
            let pooled = deposit
                .pooled
                .entry(derivation.name.clone())
                .or_default();
            for (symbol, count) in &derivation.recruited {
                let slot = pooled.entry(symbol.clone()).or_insert(0u32);
                *slot = slot.saturating_add(*count);
            }
        }
        deposit
    }

    pub fn routes(&self) -> &[Derivation] {
        &self.routes
    }

    /// Every route key, in read order.
    pub fn route_keys(&self) -> &[String] {
        &self.route_keys
    }

    /// Every declared name, with the ordinals of the artifacts declaring it.
    pub const fn declarations(&self) -> &BTreeMap<String, Vec<usize>> {
        &self.declarations
    }

    pub fn declared_names(&self) -> BTreeSet<&str> {
        self.declarations.keys().map(String::as_str).collect()
    }

    /// Whether this key names something the deposit can open.
    pub fn is_openable(&self, key: &str) -> bool {
        self.route_index.contains_key(key) || self.declarations.contains_key(key)
    }

    /// What a key recruits: one artifact's own multiset for a route key, the union over every
    /// artifact for a declared name, nothing for an atom.
    pub fn recruitment(&self, key: &str) -> Option<&BTreeMap<String, u32>> {
        if let Some(ordinal) = self.route_index.get(key) {
            return Some(&self.routes[*ordinal].recruited);
        }
        self.pooled.get(key)
    }

    /// The route keys whose recruitment carried a symbol out of a key. One entry for a route key;
    /// every artifact of the declaration that named the symbol, for a declared name.
    pub fn supplying_routes(&self, key: &str, symbol: &str) -> Vec<String> {
        if let Some(ordinal) = self.route_index.get(key) {
            return if self.routes[*ordinal].recruited.contains_key(symbol) {
                vec![key.to_owned()]
            } else {
                Vec::new()
            };
        }
        self.declarations
            .get(key)
            .map(|ordinals| {
                ordinals
                    .iter()
                    .filter(|ordinal| self.routes[**ordinal].recruited.contains_key(symbol))
                    .map(|ordinal| self.route_keys[*ordinal].clone())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The statement a key reaches: one artifact's, or the statements of every artifact of a
    /// declaration. Plural, because a declaration may reach more than one statement and this deposit
    /// contains one that does.
    pub fn statements_of(&self, key: &str) -> BTreeSet<&str> {
        if let Some(ordinal) = self.route_index.get(key) {
            return BTreeSet::from([self.routes[*ordinal].statement.as_str()]);
        }
        self.declarations
            .get(key)
            .map(|ordinals| {
                ordinals
                    .iter()
                    .map(|ordinal| self.routes[*ordinal].statement.as_str())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// **The elaboration.** The transitive recruitment closure of one key, as a complex.
    pub fn elaborate(
        &self,
        root: &str,
        aperture: ElaborationAperture,
    ) -> Result<Elaboration, ElaborationRefusal> {
        if !self.is_openable(root) {
            return Err(ElaborationRefusal::RootIsNotInTheDeposit {
                root: root.to_owned(),
            });
        }

        let mut constituents: BTreeMap<String, Constituent> = BTreeMap::new();
        constituents.insert(
            root.to_owned(),
            Constituent {
                name: root.to_owned(),
                entered_at: 0,
                depths: BTreeSet::from([0usize]),
                declared: self.is_openable(root),
                opened: false,
            },
        );

        let mut arrivals: Vec<Arrival> = Vec::new();
        let mut layer: Vec<String> = vec![root.to_owned()];
        let mut depth = 0usize;
        let mut beyond_depth: BTreeSet<String> = BTreeSet::new();

        while !layer.is_empty() {
            if !aperture.may_open(depth) {
                for key in &layer {
                    if self.is_openable(key) {
                        beyond_depth.insert(key.clone());
                    }
                }
                break;
            }
            let mut next: Vec<String> = Vec::new();
            for key in &layer {
                let Some(recruited) = self.recruitment(key) else {
                    continue;
                };
                if let Some(carried) = constituents.get_mut(key) {
                    carried.opened = true;
                }
                for (symbol, count) in recruited {
                    arrivals.push(Arrival {
                        from: key.clone(),
                        to: symbol.clone(),
                        at_depth: depth + 1,
                        occurrences: *count,
                        routes: self.supplying_routes(key, symbol),
                    });
                    match constituents.get_mut(symbol) {
                        Some(carried) => {
                            // Already opened, or queued to be. Record the further depth and do not
                            // walk it again: that is what makes a cycle terminate without being
                            // truncated, and `cycles()` returns it whole.
                            carried.depths.insert(depth + 1);
                        }
                        None => {
                            constituents.insert(
                                symbol.clone(),
                                Constituent {
                                    name: symbol.clone(),
                                    entered_at: depth + 1,
                                    depths: BTreeSet::from([depth + 1]),
                                    declared: self.is_openable(symbol),
                                    opened: false,
                                },
                            );
                            next.push(symbol.clone());
                        }
                    }
                }
            }
            layer = next;
            depth += 1;
        }

        let atoms: BTreeSet<String> = constituents
            .values()
            .filter(|carried| !carried.declared)
            .map(|carried| carried.name.clone())
            .collect();

        let mut unopened: BTreeSet<String> = BTreeSet::new();
        for key in &beyond_depth {
            let Some(recruited) = self.recruitment(key) else {
                continue;
            };
            for symbol in recruited.keys() {
                if !constituents.contains_key(symbol) {
                    unopened.insert(symbol.clone());
                }
            }
        }

        let cycles = retained_cycles(&constituents, &arrivals);
        let (complex, vertices, edges) = found_meaning_complex(&constituents, &arrivals)?;

        Ok(Elaboration {
            root: root.to_owned(),
            aperture,
            constituents,
            arrivals,
            cycles,
            atoms,
            beyond_depth,
            unopened,
            complex,
            vertices,
            edges,
        })
    }
}

/// The meaning complex with the two indices into it: constituent name to 0-cell, and recruitment
/// passage to 1-cell.
type MeaningComplex = (
    GradedCausalComplex,
    BTreeMap<String, CausalCellId>,
    BTreeMap<(String, String), CausalCellId>,
);

/// The meaning, as a complex. One 0-cell per constituent; one 1-cell per distinct recruitment
/// passage, oriented from the constituent that recruited to the one it recruited.
///
/// A self-recruitment attaches to its one vertex twice, once each hand — `(1, 1)` — which is what
/// `algebraic::ComparativeMultiplicity` documents a loop edge to be, and is not the absence of an
/// attachment.
fn found_meaning_complex(
    constituents: &BTreeMap<String, Constituent>,
    arrivals: &[Arrival],
) -> Result<MeaningComplex, CausalAlgebraicError> {
    let mut complex = GradedCausalComplex::default();
    let mut occasion = 0u64;
    let mut vertices: BTreeMap<String, CausalCellId> = BTreeMap::new();
    for name in constituents.keys() {
        occasion += 1;
        let id = complex.found_cell(
            name.clone(),
            BTreeSet::from([EventId(occasion)]),
            0,
            CausalChain::default(),
        )?;
        vertices.insert(name.clone(), id);
    }

    let passages: BTreeSet<(String, String)> = arrivals
        .iter()
        .map(|arrival| (arrival.from.clone(), arrival.to.clone()))
        .collect();

    let mut edges: BTreeMap<(String, String), CausalCellId> = BTreeMap::new();
    for (from, to) in passages {
        let (Some(source), Some(target)) = (vertices.get(&from), vertices.get(&to)) else {
            continue;
        };
        let mut boundary = CausalChain::default();
        boundary.add_term(*source, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(*target, ComparativeMultiplicity::negative(1u32));
        occasion += 1;
        let id = complex.found_cell(
            format!("{from}->{to}"),
            BTreeSet::from([EventId(occasion)]),
            1,
            boundary,
        )?;
        edges.insert((from, to), id);
    }

    Ok((complex, vertices, edges))
}

/// The strongly connected components of the arrival digraph carrying a cycle, each with a witness
/// passage that returns to its own start.
///
/// Tarjan's algorithm, written iteratively so a deep recruitment chain cannot exhaust the stack.
fn retained_cycles(
    constituents: &BTreeMap<String, Constituent>,
    arrivals: &[Arrival],
) -> Vec<RetainedCycle> {
    let nodes: Vec<&str> = constituents.keys().map(String::as_str).collect();
    let index: BTreeMap<&str, usize> = nodes
        .iter()
        .enumerate()
        .map(|(slot, name)| (*name, slot))
        .collect();
    let mut out: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); nodes.len()];
    let mut self_loops: BTreeSet<usize> = BTreeSet::new();
    for arrival in arrivals {
        let (Some(from), Some(to)) = (
            index.get(arrival.from.as_str()),
            index.get(arrival.to.as_str()),
        ) else {
            continue;
        };
        if from == to {
            self_loops.insert(*from);
        }
        out[*from].insert(*to);
    }
    let adjacency: Vec<Vec<usize>> = out.into_iter().map(|set| set.into_iter().collect()).collect();

    const UNSET: usize = usize::MAX;
    let mut number = vec![UNSET; nodes.len()];
    let mut low = vec![UNSET; nodes.len()];
    let mut on_stack = vec![false; nodes.len()];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_number = 0usize;
    let mut components: Vec<Vec<usize>> = Vec::new();

    for start in 0..nodes.len() {
        if number[start] != UNSET {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some((node, edge)) = work.pop() {
            if edge == 0 {
                number[node] = next_number;
                low[node] = next_number;
                next_number += 1;
                stack.push(node);
                on_stack[node] = true;
            }
            if edge < adjacency[node].len() {
                let child = adjacency[node][edge];
                work.push((node, edge + 1));
                if number[child] == UNSET {
                    work.push((child, 0));
                } else if on_stack[child] {
                    low[node] = low[node].min(number[child]);
                }
                continue;
            }
            // Every edge walked. Close the component, then fold into the parent.
            if low[node] == number[node] {
                let mut component = Vec::new();
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                components.push(component);
            }
            if let Some((parent, _)) = work.last().copied() {
                low[parent] = low[parent].min(low[node]);
            }
        }
    }

    let mut cycles: Vec<RetainedCycle> = Vec::new();
    for component in components {
        let carries_cycle = component.len() > 1 || component.iter().any(|at| self_loops.contains(at));
        if !carries_cycle {
            continue;
        }
        let mut members: Vec<String> = component.iter().map(|at| nodes[*at].to_owned()).collect();
        members.sort();
        let inside: BTreeSet<usize> = component.iter().copied().collect();
        let start = index[members[0].as_str()];
        let witness = witness_passage(start, &inside, &adjacency, &nodes);
        cycles.push(RetainedCycle { members, witness });
    }
    cycles.sort();
    cycles
}

/// One passage that leaves `start`, stays inside the component, and returns to `start`.
fn witness_passage(
    start: usize,
    inside: &BTreeSet<usize>,
    adjacency: &[Vec<usize>],
    nodes: &[&str],
) -> Vec<String> {
    let mut parent: BTreeMap<usize, usize> = BTreeMap::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    for child in &adjacency[start] {
        if !inside.contains(child) {
            continue;
        }
        if *child == start {
            return vec![nodes[start].to_owned(), nodes[start].to_owned()];
        }
        parent.insert(*child, start);
        queue.push_back(*child);
    }
    while let Some(node) = queue.pop_front() {
        for child in &adjacency[node] {
            if !inside.contains(child) {
                continue;
            }
            if *child == start {
                let mut back = vec![start, node];
                let mut here = node;
                while let Some(before) = parent.get(&here).copied() {
                    if before == start {
                        break;
                    }
                    back.push(before);
                    here = before;
                }
                back.push(start);
                back.reverse();
                return back.into_iter().map(|at| nodes[at].to_owned()).collect();
            }
            if !parent.contains_key(child) {
                parent.insert(*child, node);
                queue.push_back(*child);
            }
        }
    }
    vec![nodes[start].to_owned()]
}

/// Why an elaboration was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ElaborationRefusal {
    /// The root names neither a route nor a declaration this deposit carries. Refused rather than
    /// returned empty, so an elaboration of nothing cannot be read as a meaning that is empty.
    RootIsNotInTheDeposit { root: String },
    /// The meaning complex refused a cell.
    Algebra(CausalAlgebraicError),
}

impl std::fmt::Display for ElaborationRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RootIsNotInTheDeposit { root } => write!(
                formatter,
                "the deposit declares no route and no theorem named {root:?}, so there is nothing \
                 to elaborate"
            ),
            Self::Algebra(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for ElaborationRefusal {}

impl From<CausalAlgebraicError> for ElaborationRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebra(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_atlas::read_derivation;

    fn derivation(name: &str, statement: &str, recruited: &[(&str, u32)]) -> Derivation {
        Derivation {
            name: name.to_owned(),
            statement: statement.to_owned(),
            recruited: recruited
                .iter()
                .map(|(symbol, count)| ((*symbol).to_owned(), *count))
                .collect(),
        }
    }

    /// A chain: `top` names `middle`, `middle` names `bottom`, `bottom` names an atom the deposit
    /// does not declare. Three depths, and nothing at depth three is nameable from depth zero.
    fn chained_deposit() -> Vec<Derivation> {
        vec![
            derivation("top", "S", &[("middle", 1), ("visible", 1)]),
            derivation("middle", "T", &[("bottom", 1), ("halfway", 1)]),
            derivation("bottom", "U", &[("deep", 2)]),
        ]
    }

    /// Two declarations that name each other. A real cycle.
    fn mutually_recursive_deposit() -> Vec<Derivation> {
        vec![
            derivation("ping", "S", &[("pong", 1), ("shared", 1)]),
            derivation("pong", "S", &[("ping", 1), ("shared", 1)]),
        ]
    }

    // -------------------------------------------------------------- the meaning is built, not read

    #[test]
    fn a_meaning_carries_constituents_the_root_does_not_name_and_names_the_passage_that_built_them()
    {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let meaning = deposit
            .elaborate("top", ElaborationAperture::Exhausted)
            .expect("top is declared");

        // The root's own recruitment.
        assert_eq!(meaning.at_depth(1), BTreeSet::from(["middle", "visible"]));
        // Reached only by opening `middle`, and only by opening what `middle` opened.
        assert_eq!(meaning.at_depth(2), BTreeSet::from(["bottom", "halfway"]));
        assert_eq!(meaning.at_depth(3), BTreeSet::from(["deep"]));
        assert_eq!(meaning.reach(), 3);

        // `deep` is in the meaning of `top` and `top` does not name it, in either sense: it is not
        // recruited and it is not a substring.
        assert!(meaning.constructed().contains("deep"));
        assert!(!deposit.recruitment("top").expect("declared").contains_key("deep"));
        assert!(!"top".contains("deep"));

        assert_eq!(
            meaning.construction_path("deep"),
            Some(vec![
                "top".to_owned(),
                "middle".to_owned(),
                "bottom".to_owned(),
                "deep".to_owned(),
            ])
        );
    }

    #[test]
    fn the_construction_path_of_the_root_is_the_root_and_a_stranger_has_none() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let meaning = deposit
            .elaborate("top", ElaborationAperture::Exhausted)
            .expect("top is declared");
        assert_eq!(meaning.construction_path("top"), Some(vec!["top".to_owned()]));
        assert_eq!(meaning.construction_path("nowhere"), None);
    }

    #[test]
    fn a_root_the_deposit_does_not_carry_is_refused_rather_than_elaborated_to_nothing() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        assert_eq!(
            deposit
                .elaborate("absent", ElaborationAperture::Exhausted)
                .unwrap_err(),
            ElaborationRefusal::RootIsNotInTheDeposit {
                root: "absent".to_owned(),
            }
        );
    }

    // -------------------------------------------------------------------------------- the aperture

    #[test]
    fn a_depth_aperture_names_what_it_stopped_at_and_what_opening_it_would_have_brought() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let bounded = deposit
            .elaborate("top", ElaborationAperture::ToDepth(1))
            .expect("top is declared");
        assert_eq!(bounded.reach(), 1);
        // `middle` was reached and not opened; `visible` is an atom and could not have been.
        assert_eq!(bounded.beyond_depth(), &BTreeSet::from(["middle".to_owned()]));
        assert_eq!(
            bounded.unopened(),
            &BTreeSet::from(["bottom".to_owned(), "halfway".to_owned()])
        );
        assert!(!bounded.constituents().contains_key("bottom"));

        // At exhaustion both are empty: a report that the aperture was not the binding constraint.
        let exhausted = deposit
            .elaborate("top", ElaborationAperture::Exhausted)
            .expect("top is declared");
        assert!(exhausted.beyond_depth().is_empty());
        assert!(exhausted.unopened().is_empty());
    }

    #[test]
    fn depth_zero_opens_nothing_and_returns_the_root_alone() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let meaning = deposit
            .elaborate("top", ElaborationAperture::ToDepth(0))
            .expect("top is declared");
        assert_eq!(meaning.constituents().len(), 1);
        assert_eq!(meaning.beyond_depth(), &BTreeSet::from(["top".to_owned()]));
        assert_eq!(
            meaning.unopened(),
            &BTreeSet::from(["middle".to_owned(), "visible".to_owned()])
        );
    }

    #[test]
    fn an_undeclared_recruitment_is_an_atom_and_is_the_permanent_outside_of_the_deposits_aperture() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let meaning = deposit
            .elaborate("top", ElaborationAperture::Exhausted)
            .expect("top is declared");
        assert_eq!(
            meaning.atoms(),
            &BTreeSet::from([
                "deep".to_owned(),
                "halfway".to_owned(),
                "visible".to_owned(),
            ])
        );
        // An atom is reached, named, and not openable. Exhaustion does not remove it.
        for atom in meaning.atoms() {
            assert!(meaning.constituents().contains_key(atom));
            assert!(!meaning.constituents()[atom].declared);
            assert!(!meaning.constituents()[atom].opened);
        }
    }

    // ----------------------------------------------------------------------------------- the cycle

    #[test]
    fn a_mutually_recursive_pair_is_returned_as_one_cycle_and_the_walk_still_terminates() {
        let deposit = ElaborationDeposit::read(&mutually_recursive_deposit());
        let meaning = deposit
            .elaborate("ping", ElaborationAperture::Exhausted)
            .expect("ping is declared");

        assert_eq!(meaning.cycles().len(), 1);
        let cycle = &meaning.cycles()[0];
        assert_eq!(cycle.members, vec!["ping".to_owned(), "pong".to_owned()]);
        assert!(!cycle.is_self_recruitment());
        assert_eq!(
            cycle.witness,
            vec!["ping".to_owned(), "pong".to_owned(), "ping".to_owned()]
        );

        // The cycle is retained rather than truncated: `ping` carries the depth it was re-reached
        // at beside the depth it entered at, and both are in the population.
        let ping = &meaning.constituents()["ping"];
        assert_eq!(ping.entered_at, 0);
        assert_eq!(ping.depths, BTreeSet::from([0usize, 2usize]));
        assert!(meaning.edges().contains_key(&("pong".to_owned(), "ping".to_owned())));
    }

    #[test]
    fn a_declaration_that_names_itself_is_a_cycle_of_one_member() {
        let deposit =
            ElaborationDeposit::read(&[derivation("loop", "S", &[("loop", 1), ("other", 1)])]);
        let meaning = deposit
            .elaborate("loop", ElaborationAperture::Exhausted)
            .expect("loop is declared");
        assert_eq!(meaning.cycles().len(), 1);
        assert!(meaning.cycles()[0].is_self_recruitment());
        assert_eq!(meaning.cycles()[0].members, vec!["loop".to_owned()]);
        // The loop edge attaches to its one vertex twice, once each hand.
        let edge = meaning.edges()[&("loop".to_owned(), "loop".to_owned())];
        let coefficient = meaning
            .complex()
            .cell(edge)
            .expect("the edge was founded")
            .boundary
            .coefficient(meaning.vertices()["loop"]);
        assert!(!coefficient.is_zero());
        assert!(coefficient.difference_is_zero());
    }

    #[test]
    fn an_acyclic_deposit_returns_no_cycle_which_is_what_makes_the_detector_falsifiable() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let meaning = deposit
            .elaborate("top", ElaborationAperture::Exhausted)
            .expect("top is declared");
        assert!(meaning.cycles().is_empty());
    }

    // ---------------------------------------------------------------------- routes and declarations

    #[test]
    fn a_route_key_resolves_to_one_artifact_and_a_name_to_the_union_over_its_artifacts() {
        let population = vec![
            derivation("shared_name", "S", &[("left", 1)]),
            derivation("shared_name", "S", &[("right", 1)]),
        ];
        let deposit = ElaborationDeposit::read(&population);
        assert_eq!(
            deposit.recruitment("shared_name#0").expect("route"),
            &BTreeMap::from([("left".to_owned(), 1u32)])
        );
        assert_eq!(
            deposit.recruitment("shared_name").expect("declaration"),
            &BTreeMap::from([("left".to_owned(), 1u32), ("right".to_owned(), 1u32)])
        );
        // And the plurality is retained rather than summed away.
        assert_eq!(
            deposit.supplying_routes("shared_name", "left"),
            vec!["shared_name#0".to_owned()]
        );
    }

    #[test]
    fn a_name_reached_from_a_route_opens_into_every_artifact_of_that_name() {
        // The route names `helper` and nothing else the helper names. Opening the NAME is what puts
        // both artifacts' recruitment into the route's meaning, and that is the pooling rule stated
        // in the module documentation, checked rather than asserted.
        let population = vec![
            derivation("caller", "S", &[("helper", 1)]),
            derivation("helper", "T", &[("first", 1)]),
            derivation("helper", "T", &[("second", 1)]),
        ];
        let deposit = ElaborationDeposit::read(&population);
        let meaning = deposit
            .elaborate("caller#0", ElaborationAperture::Exhausted)
            .expect("the route is in the deposit");
        assert_eq!(meaning.at_depth(1), BTreeSet::from(["helper"]));
        assert_eq!(meaning.at_depth(2), BTreeSet::from(["first", "second"]));
        let arrival = meaning
            .arrivals()
            .iter()
            .find(|arrival| arrival.to == "second")
            .expect("second arrived");
        assert_eq!(arrival.routes, vec!["helper#2".to_owned()]);
    }

    // ------------------------------------------------------------------------------- the signature

    #[test]
    fn the_signature_is_the_constituents_with_their_first_depths_and_nothing_else() {
        let deposit = ElaborationDeposit::read(&chained_deposit());
        let meaning = deposit
            .elaborate("top", ElaborationAperture::Exhausted)
            .expect("top is declared");
        assert_eq!(
            meaning.signature(),
            BTreeMap::from([
                ("top", 0usize),
                ("middle", 1),
                ("visible", 1),
                ("bottom", 2),
                ("halfway", 2),
                ("deep", 3),
            ])
        );
    }

    // ------------------------------------------------------------------------- deposited material

    /// `standing/output/lean-proof-production/carrier-transport-00016.lean`, verbatim.
    const DEPOSITED_ROUTE: &str = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  rw [formal_carry]\n  assumption\nend Soma\n";

    /// `standing/output/agentic-research-kernel/formal_carry-00002.lean`, verbatim.
    const DEPOSITED_HELPER: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem formal_carry (h : P) : exactCarrier P := by\n  apply exact_chart_carry\n  assumption\nend Soma\n";

    #[test]
    fn on_deposited_material_a_routes_meaning_carries_what_the_declaration_it_named_recruits() {
        let population = vec![
            read_derivation(DEPOSITED_ROUTE).expect("declares a theorem"),
            read_derivation(DEPOSITED_HELPER).expect("declares a theorem"),
        ];
        let deposit = ElaborationDeposit::read(&population);
        let meaning = deposit
            .elaborate("carrier_transport#0", ElaborationAperture::Exhausted)
            .expect("the route is in the deposit");

        // The route names `formal_carry`; it does not name `apply` or `exact_chart_carry`.
        assert!(meaning.at_depth(1).contains("formal_carry"));
        assert!(!meaning.at_depth(1).contains("apply"));
        assert!(meaning.constructed().contains("apply"));
        assert!(meaning.constructed().contains("exact_chart_carry"));
        assert_eq!(
            meaning.construction_path("apply"),
            Some(vec![
                "carrier_transport#0".to_owned(),
                "formal_carry".to_owned(),
                "apply".to_owned(),
            ])
        );
    }
}
