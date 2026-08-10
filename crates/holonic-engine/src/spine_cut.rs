//! **Which of the spine's five cuts a chain reading is at.**
//!
//! # Why this exists
//!
//! `canon/THE_HOLOBROCHOS_SPINE.md` states the chain law
//!
//! ```text
//!   q_{k+1} − q_k + B j_k = r_k
//! ```
//!
//! and then the sentence the whole spine turns on:
//!
//! > *"circulation `j ≠ 0`, **rest**, **accumulation**, **leak**, and **short circuit** are distinct
//! > cuts."*
//!
//! with the reading rule at `:580`: *"No emission without a return edge — and name the cut. An
//! analysis terminating in `stdout` has not closed a cycle. **Report which of rest, accumulation,
//! leak, or short circuit applies.**"*
//!
//! **Five distinct cuts, not one pass/fail** — and until 2026-08-10 four had owners and the fifth had
//! none. `blueprint/THE_ROADMAP.md` carried *"the short-circuit cut has no owner"* as open work, and
//! `short_circuit` returned zero hits in every `src/` in the tree.
//!
//! **The missing object was not one organ. It was the classifier.** Naming the cut is a measurement,
//! so what was owed is the thing that takes a reading and returns which of the five it is — with the
//! other four already computable and no single place asking the question.
//!
//! # The classification, and every branch is decidable
//!
//! Given an incidence `B`, a current `j`, a residual `r`, the endpoint potentials `q_m` and `q_n`,
//! and a **declared load** — the edges the caller says the current exists to cross:
//!
//! ```text
//!   r ≠ 0 anywhere                            LEAK          current enters or leaves
//!   j = 0                                     REST          nothing flows
//!   q_n ≠ q_m                                 ACCUMULATION  the residual was stored
//!   j ≠ 0, closed, and j vanishes on the load SHORT CIRCUIT it closed without crossing the load
//!   j ≠ 0, closed, and j reaches the load     CIRCULATION   the j ≠ 0 cut proper
//! ```
//!
//! The order matters and is stated rather than left to the reader: a leak is checked first because a
//! body with a source is not at any of the closed cuts, and accumulation before the two closed cases
//! because a stored residual is not a circulation however the current is supported.
//!
//! # What a short circuit is, precisely
//!
//! **The load is the caller's declaration and is never inferred.** A short circuit is not "current
//! took a cheap path" — this module has no resistances and computes no cost. It is the exact
//! statement that a **closed, source-free, non-zero current is supported entirely off the declared
//! load**: the loop returns, and the thing it was supposed to cross was not crossed.
//!
//! That is why an empty load is refused rather than answered. With no declared load every closed
//! current is trivially a short circuit, which would make the cut a property of the declaration
//! rather than of the material — `CLAUDE.md` §8's vacuous-gauge defect exactly.
//!
//! Everything here is exact rational arithmetic. No float, no tolerance, no threshold.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::VertexId;

/// An edge of the chain, named by the caller. Local to this module: the tree carries `Edge` as a
/// vertex pair in `simplicial`, and a cut reading needs an identity independent of its endpoints
/// because a theta graph has parallel edges and they are the whole point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EdgeId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SpineCutError {
    /// A current or residual named an edge or vertex the incidence does not carry.
    #[error("the reading names edge {0:?}, which the incidence does not carry")]
    UnknownEdge(EdgeId),
    #[error("the reading names vertex {0:?}, which the incidence does not carry")]
    UnknownVertex(VertexId),
    /// **The declared load is empty.** Refused rather than answered: with no load every closed
    /// current is trivially a short circuit, which would make the cut a property of the declaration
    /// instead of the material.
    #[error("the declared load is empty, so the short-circuit cut would be vacuous")]
    LoadNotDeclared,
    /// A declared load edge is not in the incidence.
    #[error("the declared load names edge {0:?}, which the incidence does not carry")]
    LoadEdgeNotCarried(EdgeId),
}

/// One oriented edge of the chain: `tail → head`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ChainEdge {
    pub id: EdgeId,
    pub tail: VertexId,
    pub head: VertexId,
}

/// **Which of the five cuts a reading is at.** Every variant carries the evidence that decided it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpineCut {
    /// `r ≠ 0` somewhere: the body has a source or a sink, so it is not closed at all.
    Leak { at: BTreeMap<VertexId, Rat> },
    /// `j = 0` on every edge. Nothing flows.
    Rest,
    /// The endpoint potentials differ: the residual was stored rather than returned.
    Accumulation { stored: Rat },
    /// A closed, source-free, non-zero current supported **entirely off** the declared load. The
    /// loop returned and the load was never crossed.
    ShortCircuit {
        /// The edges actually carrying current, none of which is a load edge.
        bypass: BTreeSet<EdgeId>,
        /// The load the caller declared and the current did not reach.
        declared_load: BTreeSet<EdgeId>,
    },
    /// The `j ≠ 0` cut proper: closed, source-free, and reaching the load.
    Circulation {
        crossed: BTreeSet<EdgeId>,
        /// `B j`, retained so a caller can see the closure rather than take it on trust.
        divergence: BTreeMap<VertexId, Rat>,
    },
}

impl SpineCut {
    /// The cut's name, as the spine writes it.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Leak { .. } => "leak",
            Self::Rest => "rest",
            Self::Accumulation { .. } => "accumulation",
            Self::ShortCircuit { .. } => "short circuit",
            Self::Circulation { .. } => "circulation j != 0",
        }
    }

    /// Whether the body returned what it emitted. Only circulation does.
    pub fn returns(&self) -> bool {
        matches!(self, Self::Circulation { .. })
    }
}

/// One reading of the chain law at a cut.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainReading {
    pub edges: Vec<ChainEdge>,
    /// The current per edge. An absent edge carries zero.
    pub current: BTreeMap<EdgeId, Rat>,
    /// The residual per vertex. An absent vertex carries zero.
    pub residual: BTreeMap<VertexId, Rat>,
    /// `q_n − q_m`, the change in potential across the reading.
    pub potential_change: Rat,
}

impl ChainReading {
    /// `B j` — the divergence of the current at every vertex, exactly.
    pub fn divergence(&self) -> BTreeMap<VertexId, Rat> {
        let mut divergence: BTreeMap<VertexId, Rat> = BTreeMap::new();
        for edge in &self.edges {
            let flow = self.current.get(&edge.id).cloned().unwrap_or_else(Rat::zero);
            if flow.is_zero() {
                divergence.entry(edge.tail).or_insert_with(Rat::zero);
                divergence.entry(edge.head).or_insert_with(Rat::zero);
                continue;
            }
            *divergence.entry(edge.head).or_insert_with(Rat::zero) += &flow;
            *divergence.entry(edge.tail).or_insert_with(Rat::zero) -= &flow;
        }
        divergence
    }

    /// The edges actually carrying current.
    pub fn carrying(&self) -> BTreeSet<EdgeId> {
        self.current
            .iter()
            .filter(|(_, flow)| !flow.is_zero())
            .map(|(id, _)| *id)
            .collect()
    }
}

/// **Name the cut.** The declared load is the caller's and is never inferred.
pub fn name_the_cut(
    reading: &ChainReading,
    declared_load: &BTreeSet<EdgeId>,
) -> Result<SpineCut, SpineCutError> {
    if declared_load.is_empty() {
        return Err(SpineCutError::LoadNotDeclared);
    }
    let carried: BTreeSet<EdgeId> = reading.edges.iter().map(|edge| edge.id).collect();
    for edge in declared_load {
        if !carried.contains(edge) {
            return Err(SpineCutError::LoadEdgeNotCarried(*edge));
        }
    }
    for edge in reading.current.keys() {
        if !carried.contains(edge) {
            return Err(SpineCutError::UnknownEdge(*edge));
        }
    }
    let vertices: BTreeSet<VertexId> = reading
        .edges
        .iter()
        .flat_map(|edge| [edge.tail, edge.head])
        .collect();
    for vertex in reading.residual.keys() {
        if !vertices.contains(vertex) {
            return Err(SpineCutError::UnknownVertex(*vertex));
        }
    }

    // A leak first: a body with a source or a sink is not at any closed cut.
    let leaking: BTreeMap<VertexId, Rat> = reading
        .residual
        .iter()
        .filter(|(_, value)| !value.is_zero())
        .map(|(vertex, value)| (*vertex, value.clone()))
        .collect();
    if !leaking.is_empty() {
        return Ok(SpineCut::Leak { at: leaking });
    }

    let carrying = reading.carrying();
    if carrying.is_empty() {
        return Ok(SpineCut::Rest);
    }

    // Accumulation before the closed cases: a stored residual is not a circulation however the
    // current is supported.
    if !reading.potential_change.is_zero() {
        return Ok(SpineCut::Accumulation {
            stored: reading.potential_change.clone(),
        });
    }

    let crossed: BTreeSet<EdgeId> = carrying.intersection(declared_load).copied().collect();
    if crossed.is_empty() {
        return Ok(SpineCut::ShortCircuit {
            bypass: carrying,
            declared_load: declared_load.clone(),
        });
    }
    Ok(SpineCut::Circulation {
        crossed,
        divergence: reading.divergence(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn edge(id: u64, tail: u64, head: u64) -> ChainEdge {
        ChainEdge {
            id: EdgeId(id),
            tail: VertexId(tail),
            head: VertexId(head),
        }
    }

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    /// A theta graph: two vertices joined by three parallel edges. Edge 3 is the declared load.
    fn theta() -> Vec<ChainEdge> {
        vec![edge(1, 1, 2), edge(2, 2, 1), edge(3, 1, 2)]
    }

    fn load() -> BTreeSet<EdgeId> {
        BTreeSet::from([EdgeId(3)])
    }

    fn reading(current: &[(u64, i64)], residual: &[(u64, i64)], change: i64) -> ChainReading {
        ChainReading {
            edges: theta(),
            current: current.iter().map(|(e, v)| (EdgeId(*e), rat(*v))).collect(),
            residual: residual.iter().map(|(v, r)| (VertexId(*v), rat(*r))).collect(),
            potential_change: rat(change),
        }
    }

    /// **The short circuit: the loop closes through edges 1 and 2 and never touches the load.**
    #[test]
    fn a_closed_current_that_misses_the_declared_load_is_a_short_circuit() {
        let cut = name_the_cut(&reading(&[(1, 1), (2, 1)], &[], 0), &load()).unwrap();
        assert_eq!(cut.name(), "short circuit");
        assert!(!cut.returns());
        let SpineCut::ShortCircuit { bypass, .. } = &cut else {
            panic!("the bypass is exhibited");
        };
        assert_eq!(*bypass, BTreeSet::from([EdgeId(1), EdgeId(2)]));
    }

    /// The same incidence, the same closure, current through the load: circulation.
    #[test]
    fn the_same_loop_through_the_load_is_circulation() {
        let cut = name_the_cut(&reading(&[(3, 1), (2, 1)], &[], 0), &load()).unwrap();
        assert_eq!(cut.name(), "circulation j != 0");
        assert!(cut.returns());
        let SpineCut::Circulation { crossed, divergence } = &cut else {
            panic!("the crossing is exhibited");
        };
        assert_eq!(*crossed, BTreeSet::from([EdgeId(3)]));
        // Closed: the divergence vanishes at every vertex.
        assert!(divergence.values().all(Zero::is_zero));
    }

    /// **The classifier separates all five on one incidence**, which is what makes it a
    /// classification rather than a predicate wearing five names.
    #[test]
    fn all_five_cuts_are_reachable_on_one_incidence() {
        let rest = name_the_cut(&reading(&[], &[], 0), &load()).unwrap();
        let leak = name_the_cut(&reading(&[(3, 1)], &[(1, 1)], 0), &load()).unwrap();
        let accumulation = name_the_cut(&reading(&[(3, 1), (2, 1)], &[], 5), &load()).unwrap();
        let short = name_the_cut(&reading(&[(1, 1), (2, 1)], &[], 0), &load()).unwrap();
        let circulation = name_the_cut(&reading(&[(3, 1), (2, 1)], &[], 0), &load()).unwrap();

        let names: Vec<&str> = vec![
            rest.name(),
            leak.name(),
            accumulation.name(),
            short.name(),
            circulation.name(),
        ];
        assert_eq!(
            names,
            vec!["rest", "leak", "accumulation", "short circuit", "circulation j != 0"]
        );
        // and exactly one of them returns.
        assert_eq!(
            [&rest, &leak, &accumulation, &short, &circulation]
                .iter()
                .filter(|cut| cut.returns())
                .count(),
            1
        );
    }

    /// A leak outranks a closed current: a body with a source is not at a closed cut.
    #[test]
    fn a_source_is_named_a_leak_even_when_the_current_closes() {
        let cut = name_the_cut(&reading(&[(3, 1), (2, 1)], &[(2, -3)], 0), &load()).unwrap();
        assert_eq!(cut.name(), "leak");
    }

    /// **An undeclared load is refused, not answered.** With no load every closed current is
    /// trivially a short circuit, which would make the cut a property of the declaration.
    #[test]
    fn an_empty_load_is_refused_because_the_cut_would_be_vacuous() {
        let refusal = name_the_cut(&reading(&[(1, 1), (2, 1)], &[], 0), &BTreeSet::new());
        assert_eq!(refusal, Err(SpineCutError::LoadNotDeclared));
    }

    /// A load edge the incidence does not carry is refused by name.
    #[test]
    fn a_load_edge_outside_the_incidence_is_refused_by_name() {
        let refusal = name_the_cut(
            &reading(&[(1, 1)], &[], 0),
            &BTreeSet::from([EdgeId(99)]),
        );
        assert_eq!(refusal, Err(SpineCutError::LoadEdgeNotCarried(EdgeId(99))));
    }
}
