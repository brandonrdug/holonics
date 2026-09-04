//! **Which of the spine's five cuts a chain reading is at.**
//!
//! # Why this exists
//!
//! `docs/canon/THE_HOLOBROCHOS_SPINE.md` states the chain law
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
//! none. `docs/plans/THE_ROADMAP.md` carried *"the short-circuit cut has no owner"* as open work, and
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
//! # The mouth
//!
//! [`read_the_chain`] is where a live chain enters: a [`GradedCausalComplex`] supplies `B` and a
//! [`CausalChain`] over it supplies `j`, and the residual `r = B j` is computed rather than
//! declared. Until 2026-08-10 this module had no such mouth and its only material was the theta
//! graph in its own tests, so the cut it names had never been read off anything the body produces.
//! `examples/the_cut_is_named_on_real_material.rs` drives it over the conditioned derivation circuit
//! of the deposited Lean production and reaches all five cuts.
//!
//! Everything here is exact rational arithmetic. No float, no tolerance, no threshold.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::VertexId;
use crate::algebraic::{CausalCell, CausalCellId, CausalChain, GradedCausalComplex};
use crate::inertia::{InertiaError, SymmetricForm, inertia};
use crate::running_integral::PotentialSearch;

// ---------------------------------------------------------------------------------------------
// where q comes from
// ---------------------------------------------------------------------------------------------

/// **The chain law's `q_n − q_m`, read off a potential instead of taken from the caller.**
///
/// [`read_the_chain`] takes `potential_change` as a scalar and says of it: *"it is a line integral
/// of a cochain this module does not carry and must not guess."* That refusal was honest and it
/// left an edge open — [`crate::running_integral::found_potential_in`], in this same crate, returns
/// exactly the grade-zero cochain the integral is a difference of, and nothing joined them. This is
/// the join.
///
/// # What the join exposes, which is the reason to build it rather than plumb it
///
/// `q_n − q_m` is a difference of a **potential**, and a potential exists exactly when the drive is
/// a coboundary. Where the drive carries holonomy — a chord whose residual does not vanish in the
/// declared group — the sum along a walk from `m` to `n` is walk-dependent, so there is no such
/// difference at all. **The chain law's `q` term presupposes trivial cohomology**, and on a body
/// with a standing winding the ACCUMULATION cut is not merely unknown but ill-posed until a walk is
/// declared.
///
/// That is the ant and the spider arriving at the spine: the ant rebuilds the position by walking
/// and the spider carries what the loop deposited, and `q` is the ant's half. Asking for it on
/// material the spider owns is the error this refusal names, so the return is a `Result` and
/// [`SpineCutError::PotentialIsPathDependent`] is a first-class answer rather than a failure.
///
/// The group is the caller's — it reaches here through the `PotentialSearch` it declared — so a
/// drive whose only chords are even is path-dependent over `ℤ` and path-*independent* over `ℤ/2`,
/// and the same material returns a potential change in one declared group and a refusal in the
/// other. Neither is more true; they are two receivers.
pub fn potential_change(
    search: &PotentialSearch,
    from: CausalCellId,
    to: CausalCellId,
) -> Result<Rat, SpineCutError> {
    if let Some(first) = search.retained_obstructions.first() {
        return Err(SpineCutError::PotentialIsPathDependent {
            chords: search.retained_obstructions.len(),
            first: first.cell,
        });
    }
    for endpoint in [from, to] {
        if !search.reached.contains(&endpoint) {
            return Err(SpineCutError::EndpointNotReached(endpoint));
        }
    }
    Ok(Rat::from_integer(
        search.potential.value(to) - search.potential.value(from),
    ))
}

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
    /// A grade-1 cell of a supplied complex does not carry exactly one `+1` head and one `-1` tail,
    /// so it has no tail and head to read and the chain law cannot be posed over it. Refused by
    /// name rather than approximated.
    #[error(
        "cell {0:?} is not a joinable one-cell: a chain reading needs one +1 head and one -1 tail"
    )]
    UnjoinableCell(CausalCellId),
    /// **`q_n − q_m` was asked of a cochain that admits no potential.** The drive carries at least
    /// one chord whose residual did not vanish in the declared group, so the sum along a walk from
    /// `m` to `n` depends on which walk is taken. There is no difference of a potential to return
    /// and this organ will not pick a walk on the caller's behalf.
    #[error(
        "the drive admits no potential in the declared group: {chords} chord(s) stand, the first at \
         {first:?}, so q_n - q_m depends on the walk"
    )]
    PotentialIsPathDependent { chords: usize, first: CausalCellId },
    /// An endpoint the potential search never reached. Its `q` is not zero; it is undefined, and
    /// returning zero would read an unvisited component as one that accumulated nothing.
    #[error("the potential search never reached {0:?}, so its q is undefined rather than zero")]
    EndpointNotReached(CausalCellId),
    /// **A declared transfer whose population the material does not carry.** Refused rather than
    /// read as zero, for the same reason [`SpineCutError::EndpointNotReached`] is: an absent count
    /// and a count of nothing are different readings, and only one of them says the loop closed.
    #[error(
        "the transfer {name} names a population the material does not carry, and an absent count \
         is not a count of zero"
    )]
    PopulationNotCarried { edge: EdgeId, name: String },
    /// An attention reading whose weight and value tables do not meet: `weights` is
    /// `queries × keys` and `values` is `keys × extent`, and both must agree on the key count.
    #[error(
        "the head's tables do not meet: {queries} queries by {keys} keys against {rows} value rows"
    )]
    HeadTablesDoNotMeet {
        queries: usize,
        keys: usize,
        rows: usize,
    },
    /// The declared sink is not a position of the head.
    #[error("position {0} is not a position of this head, so it cannot be the declared sink")]
    PositionOutsideTheHead(usize),
    /// An attention row that does not sum to one. Refused rather than normalized: a row that is not
    /// stochastic is not an attention distribution, and normalizing it here would author the
    /// material the classification is read off.
    #[error("attention row {query} sums to {total}, and an attention row is stochastic")]
    AttentionRowIsNotStochastic { query: usize, total: Rat },
    /// No read position was declared, so the delivery load would be empty and the short-circuit cut
    /// vacuous — the same refusal [`SpineCutError::LoadNotDeclared`] carries, one level up.
    #[error("no read position was declared, so the head's delivery load would be vacuous")]
    ReadPositionsNotDeclared,
    /// **The declared species is not the species the diagnostics read.** This is the refusal the
    /// mislabelled control fires: a classifier that cannot disagree with its label has classified
    /// nothing.
    #[error("the head was declared {declared:?} and its diagnostics read {read:?}")]
    SinkSpeciesRefuted {
        declared: SinkSpecies,
        read: SinkReading,
    },
    #[error(transparent)]
    Inertia(#[from] InertiaError),
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
            let flow = self
                .current
                .get(&edge.id)
                .cloned()
                .unwrap_or_else(Rat::zero);
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

/// The `-1` face and the `+1` face of a 1-cell, read off the cell's own boundary.
fn oriented_ends(cell: &CausalCell) -> Result<(VertexId, VertexId), SpineCutError> {
    let mut tail = None;
    let mut head = None;
    for (vertex, coefficient) in cell.boundary.coefficients() {
        if !coefficient.is_unit_orientation() {
            return Err(SpineCutError::UnjoinableCell(cell.id));
        }
        let slot = if coefficient.difference().is_one() {
            &mut head
        } else {
            &mut tail
        };
        if slot.replace(VertexId(vertex.0)).is_some() {
            return Err(SpineCutError::UnjoinableCell(cell.id));
        }
    }
    match (tail, head) {
        (Some(tail), Some(head)) => Ok((tail, head)),
        _ => Err(SpineCutError::UnjoinableCell(cell.id)),
    }
}

/// **Read a chain reading off the body's own carriers.**
///
/// This module was written against a hand-made incidence and had no mouth onto the chain carrier
/// every other organ in this crate already conducts through. That is the missing edge and this is
/// it: a [`GradedCausalComplex`] supplies `B` — every grade-1 cell, its tail and head read off the
/// cell's own boundary — and a [`CausalChain`] over that complex supplies `j`. A cell address is a
/// [`CausalCellId`] and carries its own grade, so grade-1 addresses become [`EdgeId`]s and grade-0
/// addresses become [`VertexId`]s with no renumbering; a vertex offered as a load edge is therefore
/// refused by [`SpineCutError::LoadEdgeNotCarried`] rather than silently accepted.
///
/// **The residual is not a parameter.** At unchanged storage the chain law reads `r = B j`, so it is
/// computed here from the incidence and the current and cannot be declared into a reading the
/// material does not support. Hand a cycle and `r` vanishes and the reading reaches the closed cuts;
/// hand an open path and the source and the sink are returned by name and the cut is a leak. That
/// asymmetry is the whole of *"no emission without a return edge"*, and it is decided by the
/// material rather than by the caller.
///
/// `potential_change` is `q_n − q_m` and stays the caller's: it is a line integral of a cochain this
/// module does not carry and must not guess.
pub fn read_the_chain(
    complex: &GradedCausalComplex,
    current: &CausalChain,
    potential_change: Rat,
) -> Result<ChainReading, SpineCutError> {
    let mut edges = Vec::new();
    for cell in complex.cells().values().filter(|cell| cell.grade == 1) {
        let (tail, head) = oriented_ends(cell)?;
        edges.push(ChainEdge {
            id: EdgeId(cell.id.0),
            tail,
            head,
        });
    }
    let carried: BTreeSet<EdgeId> = edges.iter().map(|edge| edge.id).collect();

    let mut flows: BTreeMap<EdgeId, Rat> = BTreeMap::new();
    for (cell, coefficient) in current.coefficients() {
        let id = EdgeId(cell.0);
        if !carried.contains(&id) {
            return Err(SpineCutError::UnknownEdge(id));
        }
        flows.insert(id, Rat::from_integer(coefficient.difference()));
    }

    let mut reading = ChainReading {
        edges,
        current: flows,
        residual: BTreeMap::new(),
        potential_change,
    };
    reading.residual = reading.divergence();
    Ok(reading)
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

// ---------------------------------------------------------------------------------------------
// the counted mouth — a chain whose current is a population a receipt states
// ---------------------------------------------------------------------------------------------

/// One declared transfer between two counted stations.
///
/// The **stations and the edges between them are the caller's declared reading**; the population is
/// the material's. That split is the whole discipline of this mouth: a reading that both declares
/// the structure and supplies the numbers has measured nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CountedTransfer {
    pub id: EdgeId,
    pub tail: VertexId,
    pub head: VertexId,
    /// What the caller calls this transfer, used only to name a refusal.
    pub name: String,
    /// The population the material states this transfer carried. `None` is a refusal, never a zero.
    pub population: Option<Rat>,
}

/// **A chain reading whose current is a counted population, refusing an absent count by name.**
///
/// [`read_the_chain`] reads a current off a [`CausalChain`] the body already carries. This is the
/// other mouth: material that states its own populations — a sealed receipt, a census, a returned
/// ledger — where the chain is a reading *of* those numbers and the closure is a question about
/// them.
///
/// The refusal is the point. A station whose figure the receipt does not carry must not enter as a
/// zero, because a zero is a claim that nothing crossed and an absence is a claim that nothing is
/// known. Reading the second as the first is how a chain comes out closed for want of a field, and
/// it is the same defect [`SpineCutError::EndpointNotReached`] already refuses one level down.
///
/// The residual is computed, never declared, exactly as in [`read_the_chain`].
pub fn read_counted_transfers(
    transfers: impl IntoIterator<Item = CountedTransfer>,
    potential_change: Rat,
) -> Result<ChainReading, SpineCutError> {
    let mut edges = Vec::new();
    let mut current = BTreeMap::new();
    for transfer in transfers {
        let population = transfer
            .population
            .ok_or(SpineCutError::PopulationNotCarried {
                edge: transfer.id,
                name: transfer.name.clone(),
            })?;
        edges.push(ChainEdge {
            id: transfer.id,
            tail: transfer.tail,
            head: transfer.head,
        });
        current.insert(transfer.id, population);
    }
    let mut reading = ChainReading {
        edges,
        current,
        residual: BTreeMap::new(),
        potential_change,
    };
    reading.residual = reading.divergence();
    Ok(reading)
}

// ---------------------------------------------------------------------------------------------
// the exterior control — an attention sink as a named cut
// ---------------------------------------------------------------------------------------------

/// The two published sink species, `docs/canon/THE_CORRESPONDENCE_ATLAS.md` §4 *"the sink as a named
/// cut"*.
///
/// - **`Nop`** — `arXiv:2605.08453`, which proves a sink is a **hard attention switch**: attention
///   concentrates on a null position whose value contributes nothing, and the head's output is
///   identically zero. Nothing is transported.
/// - **`Broadcast`** — `arXiv:2606.08105`: the sink **aggregates** from the context and
///   **redistributes** the aggregate to the queries, which is why the outputs come out low rank.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SinkSpecies {
    Nop,
    Broadcast,
}

/// What the two structural diagnostics read, **including the refusal to name a species**.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SinkReading {
    Species(SinkSpecies),
    /// The diagnostics match neither published species, and the reason is named. A classifier with
    /// no such return would assign one of two labels to every head it was ever handed, which is a
    /// check whose material cannot vary the property under test.
    Neither {
        why: &'static str,
    },
}

/// **The two published diagnostics, and nothing else.**
///
/// The falsifier the atlas row states is that the species must be separated *from value-norm and
/// output-rank readings alone*. Both are here, both exact:
///
/// - **the value mass** `Σ_i |v[i]|`, the `ℓ¹` norm. `ℓ²` is used in the papers and is not rational,
///   and the diagnostic only ever asks whether the norm is **negligible** — which for an exact
///   carrier means zero, and zero is the same set in every norm. So `ℓ¹` loses nothing the
///   diagnostic uses and keeps the reading exact.
/// - **the output rank** of `O = A·V`, computed as the rank of `OᵀO` by [`crate::inertia`]'s exact
///   elimination. `rank(OᵀO) = rank(O)` over an ordered field, so no separate rank organ is founded.
///
/// [`SinkDiagnostics::full_rank_bound`] is `min(queries, value extent)` — read off the material —
/// so "low rank" is a strict inequality against what this head could have reached and never against
/// an authored level.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SinkDiagnostics {
    pub sink: usize,
    /// `‖v_sink‖₁`. The nop diagnostic is that this is negligible.
    pub sink_value_mass: Rat,
    /// `‖v_k‖₁` at every position, so a reader can see the sink against its context rather than
    /// alone.
    pub value_masses: Vec<Rat>,
    /// `rank(A·V)`. The broadcast diagnostic is that this is strictly below the bound.
    pub output_rank: usize,
    /// `min(queries, value extent)` — what this head's output could have reached.
    pub full_rank_bound: usize,
    /// The share of the whole attention mass that lands on the sink. A measurement, never a
    /// decider: no branch below consults it.
    pub attention_on_sink: Rat,
}

impl SinkDiagnostics {
    /// **The species, from the two diagnostics alone.** No branch here reads the attention
    /// concentration, the declared label, or the chain.
    pub fn species(&self) -> SinkReading {
        let silent = self.sink_value_mass.is_zero();
        match (silent, self.output_rank) {
            (true, 0) => SinkReading::Species(SinkSpecies::Nop),
            (true, _) => SinkReading::Neither {
                why: "the sink carries no value mass and the output is not identically zero",
            },
            (false, 0) => SinkReading::Neither {
                why: "the sink carries value mass and the output is identically zero",
            },
            (false, rank) if rank < self.full_rank_bound => {
                SinkReading::Species(SinkSpecies::Broadcast)
            }
            (false, _) => SinkReading::Neither {
                why: "the output reaches the full rank this head could carry, so nothing is \
                      redistributed through one position",
            },
        }
    }
}

/// **One attention head's declared readings, exact over the rationals.**
///
/// A fixture, and it is declared material: the weights and the value vectors are the caller's, the
/// classification is not. Construction refuses a table that does not meet, a row that is not
/// stochastic, and an undeclared read set.
///
/// # The chain this becomes, and the one reading it declares
///
/// The incidence is the head's own connectivity — every ordered pair of distinct positions is an
/// edge, whether or not it carries. Self-attention is **not** an edge: a cell whose two ends are
/// one vertex has no tail and head, which [`oriented_ends`] already refuses one level down, and a
/// position attending itself transports nothing between positions.
///
/// The current is the **transported value mass**, and the sink's two directions are read
/// separately because they are two different transports:
///
/// ```text
///   k -> sink     A[sink][k] · ‖v_k‖₁          what k contributes to the sink's aggregate
///   sink -> q     γ_q · ‖v_sink‖₁              q's SHARE of the sink's value mass,
///                   γ_q = A[q][sink] / Σ_p A[p][sink]
///   k -> q        A[q][k] · ‖v_k‖₁             direct transport between context positions
/// ```
///
/// **The share is the reading, and it is declared rather than obvious.** A broadcast fans **one**
/// object out to many receivers; counting the copies would make every fan-out a source and every
/// broadcast a leak by arithmetic rather than by the material. The share is the receiver-relative
/// reading in which the hub conserves, and its total out is `‖v_sink‖₁` exactly once. The other
/// reading — copies — is lawful and is a different receiver; it is named here so that the choice is
/// visible instead of built in.
///
/// # What closure then means, and it is a property of the head rather than of this code
///
/// Under that reading the divergence at the sink is `Σ_k A[sink][k]‖v_k‖₁ − ‖v_sink‖₁`, which
/// vanishes exactly when the sink's value carries the mass it aggregated; and at a context position
/// it vanishes exactly when the share it receives back equals what it contributed. Those two
/// conditions **are** *"aggregates and redistributes"*, stated so they can fail — and a head that
/// fails either is a **leak**, with the source and the sink named. That is the honest reading of a
/// general head: content enters and leaves a layer, and only the two sink species close.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttentionHead {
    weights: Vec<Vec<Rat>>,
    values: Vec<Vec<Rat>>,
    sink: usize,
    read: BTreeSet<usize>,
}

impl AttentionHead {
    /// Declare a head. `weights` is `positions × positions`, row-stochastic; `values` is
    /// `positions × extent`; `read` is the population of query positions whose output the caller
    /// actually consumes, which is what the delivery load is built from.
    pub fn declare(
        weights: Vec<Vec<Rat>>,
        values: Vec<Vec<Rat>>,
        sink: usize,
        read: impl IntoIterator<Item = usize>,
    ) -> Result<Self, SpineCutError> {
        let positions = weights.len();
        let keys = weights.first().map_or(0, Vec::len);
        if keys != positions || values.len() != positions {
            return Err(SpineCutError::HeadTablesDoNotMeet {
                queries: positions,
                keys,
                rows: values.len(),
            });
        }
        let extent = values.first().map_or(0, Vec::len);
        for row in &values {
            if row.len() != extent {
                return Err(SpineCutError::HeadTablesDoNotMeet {
                    queries: positions,
                    keys,
                    rows: values.len(),
                });
            }
        }
        for (query, row) in weights.iter().enumerate() {
            if row.len() != positions {
                return Err(SpineCutError::HeadTablesDoNotMeet {
                    queries: positions,
                    keys: row.len(),
                    rows: values.len(),
                });
            }
            let total = row.iter().fold(Rat::zero(), |sum, weight| sum + weight);
            if total != Rat::one() {
                return Err(SpineCutError::AttentionRowIsNotStochastic { query, total });
            }
        }
        if sink >= positions {
            return Err(SpineCutError::PositionOutsideTheHead(sink));
        }
        let read: BTreeSet<usize> = read.into_iter().collect();
        if read.is_empty() {
            return Err(SpineCutError::ReadPositionsNotDeclared);
        }
        if let Some(outside) = read.iter().find(|position| **position >= positions) {
            return Err(SpineCutError::PositionOutsideTheHead(*outside));
        }
        Ok(Self {
            weights,
            values,
            sink,
            read,
        })
    }

    pub fn positions(&self) -> usize {
        self.weights.len()
    }

    pub const fn sink(&self) -> usize {
        self.sink
    }

    /// `‖v_k‖₁`, exactly.
    pub fn value_mass(&self, position: usize) -> Result<Rat, SpineCutError> {
        let row = self
            .values
            .get(position)
            .ok_or(SpineCutError::PositionOutsideTheHead(position))?;
        Ok(row.iter().fold(Rat::zero(), |sum, entry| sum + entry.abs()))
    }

    /// `O = A·V`, exactly.
    pub fn output(&self) -> Vec<Vec<Rat>> {
        let extent = self.values.first().map_or(0, Vec::len);
        self.weights
            .iter()
            .map(|row| {
                (0..extent)
                    .map(|column| {
                        row.iter()
                            .zip(&self.values)
                            .fold(Rat::zero(), |sum, (weight, value)| {
                                sum + weight * &value[column]
                            })
                    })
                    .collect()
            })
            .collect()
    }

    /// `rank(O)`, by `rank(OᵀO)` through the exact inertia elimination.
    pub fn output_rank(&self) -> Result<usize, SpineCutError> {
        let output = self.output();
        let extent = output.first().map_or(0, Vec::len);
        let gram: Vec<Vec<Rat>> = (0..extent)
            .map(|left| {
                (0..extent)
                    .map(|right| {
                        output
                            .iter()
                            .fold(Rat::zero(), |sum, row| sum + &row[left] * &row[right])
                    })
                    .collect()
            })
            .collect();
        Ok(inertia(&SymmetricForm::from_rows(gram)?).rank())
    }

    /// The two diagnostics, together with the measurements a reader needs to see them in context.
    pub fn diagnose(&self) -> Result<SinkDiagnostics, SpineCutError> {
        let positions = self.positions();
        let value_masses = (0..positions)
            .map(|position| self.value_mass(position))
            .collect::<Result<Vec<Rat>, SpineCutError>>()?;
        let attention_on_sink = self
            .weights
            .iter()
            .fold(Rat::zero(), |sum, row| sum + &row[self.sink])
            / Rat::from_integer(num_bigint::BigInt::from(positions as i64));
        Ok(SinkDiagnostics {
            sink: self.sink,
            sink_value_mass: value_masses[self.sink].clone(),
            value_masses,
            output_rank: self.output_rank()?,
            full_rank_bound: positions.min(self.values.first().map_or(0, Vec::len)),
            attention_on_sink,
        })
    }

    /// The identity of the edge `tail → head`, in this head's own numbering.
    pub fn edge(&self, tail: usize, head: usize) -> EdgeId {
        EdgeId((tail * self.positions() + head) as u64)
    }

    /// **The delivery load**: every edge whose head is a declared read position. That is what the
    /// head exists to do — deliver content to the positions someone consumes — and it is read off
    /// the declaration rather than inferred from where the current happened to go.
    pub fn delivery_load(&self) -> BTreeSet<EdgeId> {
        let positions = self.positions();
        let mut load = BTreeSet::new();
        for tail in 0..positions {
            for head in &self.read {
                if tail != *head {
                    load.insert(self.edge(tail, *head));
                }
            }
        }
        load
    }

    /// The chain reading. See this type's head for what the current is and why.
    pub fn read_the_head(&self) -> Result<ChainReading, SpineCutError> {
        let positions = self.positions();
        let masses = (0..positions)
            .map(|position| self.value_mass(position))
            .collect::<Result<Vec<Rat>, SpineCutError>>()?;
        let attending_the_sink = (0..positions)
            .filter(|query| *query != self.sink)
            .fold(Rat::zero(), |sum, query| {
                sum + &self.weights[query][self.sink]
            });

        let mut edges = Vec::new();
        let mut current = BTreeMap::new();
        for tail in 0..positions {
            for head in 0..positions {
                if tail == head {
                    continue;
                }
                let flow = if tail == self.sink {
                    // The share, never a copy: `γ_q · ‖v_sink‖₁`.
                    if attending_the_sink.is_zero() {
                        Rat::zero()
                    } else {
                        &self.weights[head][self.sink] / &attending_the_sink * &masses[self.sink]
                    }
                } else {
                    &self.weights[head][tail] * &masses[tail]
                };
                let id = self.edge(tail, head);
                edges.push(ChainEdge {
                    id,
                    tail: VertexId(tail as u64),
                    head: VertexId(head as u64),
                });
                if !flow.is_zero() {
                    current.insert(id, flow);
                }
            }
        }
        let mut reading = ChainReading {
            edges,
            current,
            // **No storage term.** A single head's attention map does not carry the residual stream,
            // which is where a transformer stores, so declaring a `q_n − q_m` here would be the
            // guess `potential_change` refuses to make. The accumulation cut is therefore not
            // reachable on this material, and that is a property of the material.
            residual: BTreeMap::new(),
            potential_change: Rat::zero(),
        };
        reading.residual = reading.divergence();
        Ok(reading)
    }
}

/// What classifying one head returns: the species the diagnostics read, the cut the chain is at,
/// and the diagnostics themselves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SinkVerdict {
    pub read: SinkReading,
    pub cut: SpineCut,
    pub diagnostics: SinkDiagnostics,
}

impl SinkVerdict {
    /// **Whether the cut and the species agree.** A nop transports nothing, so its cut is rest; a
    /// broadcast transports through one position, so its cut is closed — circulation when the hub
    /// reaches the declared load and a short circuit when it does not.
    ///
    /// This is a measured agreement between two independent readings of one head — the diagnostics
    /// never see the chain and the chain never sees the diagnostics — so it can fail, which is what
    /// makes it evidence.
    pub fn agrees(&self) -> bool {
        match (&self.read, &self.cut) {
            (SinkReading::Species(SinkSpecies::Nop), SpineCut::Rest) => true,
            (
                SinkReading::Species(SinkSpecies::Broadcast),
                SpineCut::Circulation { .. } | SpineCut::ShortCircuit { .. },
            ) => true,
            _ => false,
        }
    }
}

/// **Classify a head against the species it was declared to be, refusing a mislabel by name.**
///
/// The diagnostics are computed from the material and never consult `declared`; the declaration is
/// compared afterwards. That order is the whole content: a classifier that read the label first
/// could not disagree with it, and `CLAUDE.md` §8 — *a check whose material cannot vary the property
/// under test is the same defect as a check that cannot fail* — convicts exactly that.
pub fn classify_sink(
    head: &AttentionHead,
    declared: SinkSpecies,
) -> Result<SinkVerdict, SpineCutError> {
    let diagnostics = head.diagnose()?;
    let read = diagnostics.species();
    if read != SinkReading::Species(declared) {
        return Err(SpineCutError::SinkSpeciesRefuted { declared, read });
    }
    let reading = head.read_the_head()?;
    Ok(SinkVerdict {
        cut: name_the_cut(&reading, &head.delivery_load())?,
        read,
        diagnostics,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EventId;
    use crate::algebraic::ComparativeMultiplicity;
    use crate::running_integral::{Cochain, CoefficientGroup, found_potential_in};
    use num_bigint::BigInt;

    /// A hollow square `a→b→c` against `a→d→c`. It has one independent cycle, so a drive on it
    /// either telescopes or stands, and which one is a property of the drive rather than of the
    /// shape.
    fn vertex(complex: &mut GradedCausalComplex, name: &str) -> CausalCellId {
        complex
            .found_cell(name, [EventId(1)].into(), 0, CausalChain::default())
            .expect("a vertex has an empty boundary")
    }

    fn arc(
        complex: &mut GradedCausalComplex,
        name: &str,
        tail: CausalCellId,
        head: CausalCellId,
    ) -> CausalCellId {
        let mut boundary = CausalChain::default();
        boundary.add_term(head, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(tail, ComparativeMultiplicity::negative(1u32));
        complex
            .found_cell(name, [EventId(1)].into(), 1, boundary)
            .expect("an arc joins two vertices")
    }

    fn square() -> (GradedCausalComplex, [CausalCellId; 4], [CausalCellId; 4]) {
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let c = vertex(&mut complex, "c");
        let d = vertex(&mut complex, "d");
        let arcs = [
            arc(&mut complex, "ab", a, b),
            arc(&mut complex, "bc", b, c),
            arc(&mut complex, "ad", a, d),
            arc(&mut complex, "dc", d, c),
        ];
        (complex, [a, b, c, d], arcs)
    }

    fn drive(arcs: &[CausalCellId; 4], values: [i64; 4]) -> Cochain {
        Cochain::from_values(
            1,
            arcs.iter()
                .zip(values)
                .map(|(cell, value)| (*cell, BigInt::from(value))),
        )
    }

    /// **`q` is supplied by the potential, and refused where no potential exists.**
    ///
    /// The three returns are the whole content: a telescoping drive gives the exact difference; a
    /// drive carrying a standing chord has no difference to give and says so; and whether it stands
    /// is a question about the DECLARED GROUP, so the same material answers both ways.
    #[test]
    fn the_potential_supplies_q_and_refuses_it_where_the_drive_carries_a_winding() {
        let (complex, [a, _b, c, _d], arcs) = square();

        // Both walks a->c cost 3, so this drive is a coboundary and q_c - q_a is exact.
        let telescoping = drive(&arcs, [1, 2, 2, 1]);
        let search = found_potential_in(&complex, &telescoping, a, CoefficientGroup::Integers)
            .expect("the drive is a one-cochain and the base is a vertex");
        assert!(search.retained_obstructions.is_empty());
        assert_eq!(
            potential_change(&search, a, c).expect("a coboundary has a potential"),
            Rat::from_integer(BigInt::from(3))
        );

        // Now the two walks disagree by 2: the drive carries a winding and q is walk-dependent.
        let standing = drive(&arcs, [1, 2, 2, 3]);
        let over_integers = found_potential_in(&complex, &standing, a, CoefficientGroup::Integers)
            .expect("the drive is a one-cochain and the base is a vertex");
        assert_eq!(over_integers.retained_obstructions.len(), 1);
        match potential_change(&over_integers, a, c) {
            Err(SpineCutError::PotentialIsPathDependent { chords: 1, .. }) => {}
            other => panic!("a standing chord must refuse q, returned {other:?}"),
        }

        // The residual is 2, so mod 2 the same drive IS a coboundary and q returns. The group is
        // the caller's declaration and it decides the question, which is what makes this a
        // receiver rather than a fact about the material.
        let over_two = found_potential_in(
            &complex,
            &standing,
            a,
            CoefficientGroup::cyclic(BigInt::from(2)).expect("2 is a positive modulus"),
        )
        .expect("the drive is a one-cochain and the base is a vertex");
        assert!(over_two.retained_obstructions.is_empty());
        assert!(
            potential_change(&over_two, a, c).is_ok(),
            "the same material returns q in one declared group and refuses it in another"
        );

        // And an endpoint the walk never reached is undefined, never zero.
        let (mut apart, _, _) = square();
        let island = vertex(&mut apart, "island");
        let search = found_potential_in(&apart, &telescoping, a, CoefficientGroup::Integers)
            .expect("the drive is a one-cochain and the base is a vertex");
        match potential_change(&search, a, island) {
            Err(SpineCutError::EndpointNotReached(cell)) => assert_eq!(cell, island),
            other => panic!("an unreached endpoint must refuse, returned {other:?}"),
        }
    }

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
            residual: residual
                .iter()
                .map(|(v, r)| (VertexId(*v), rat(*r)))
                .collect(),
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
        let SpineCut::Circulation {
            crossed,
            divergence,
        } = &cut
        else {
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
            vec![
                "rest",
                "leak",
                "accumulation",
                "short circuit",
                "circulation j != 0"
            ]
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
        let refusal = name_the_cut(&reading(&[(1, 1)], &[], 0), &BTreeSet::from([EdgeId(99)]));
        assert_eq!(refusal, Err(SpineCutError::LoadEdgeNotCarried(EdgeId(99))));
    }

    // --- the mouth ------------------------------------------------------------------------------

    mod the_mouth {
        use super::*;
        use crate::algebraic::{
            CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
        };
        use crate::causal::EventId;

        fn source() -> BTreeSet<EventId> {
            BTreeSet::from([EventId(1)])
        }

        fn zero_cell(complex: &mut GradedCausalComplex, name: &str) -> CausalCellId {
            complex
                .found_cell(name, source(), 0, CausalChain::default())
                .expect("a vertex carries no boundary")
        }

        fn one_cell(
            complex: &mut GradedCausalComplex,
            name: &str,
            tail: CausalCellId,
            head: CausalCellId,
        ) -> CausalCellId {
            let mut boundary = CausalChain::default();
            boundary.add_term(head, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(tail, ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(name, source(), 1, boundary)
                .expect("an edge closes")
        }

        /// `a -> b` by two parallel one-cells, so a cycle and an open path live on one incidence.
        fn two_lane() -> (
            GradedCausalComplex,
            CausalCellId,
            CausalCellId,
            CausalCellId,
        ) {
            let mut complex = GradedCausalComplex::default();
            let a = zero_cell(&mut complex, "a");
            let b = zero_cell(&mut complex, "b");
            let left = one_cell(&mut complex, "left", a, b);
            let right = one_cell(&mut complex, "right", a, b);
            (complex, a, left, right)
        }

        fn walk(terms: &[(CausalCellId, i8)]) -> CausalChain {
            let mut chain = CausalChain::default();
            for (cell, hand) in terms {
                chain.add_term(
                    *cell,
                    ComparativeMultiplicity::from_hand(*hand, 1u32).expect("a unit hand"),
                );
            }
            chain
        }

        /// **The asymmetry the mouth exists for.** The same two cells: as a cycle the residual the
        /// mouth computes vanishes and the reading reaches a closed cut; as an open path it does
        /// not, and the source and the sink are returned by name. Neither residual was supplied.
        #[test]
        fn the_residual_is_computed_from_the_incidence_and_not_declared() {
            let (complex, _, left, right) = two_lane();
            let load = BTreeSet::from([EdgeId(left.0)]);

            let closed = read_the_chain(&complex, &walk(&[(left, 1), (right, -1)]), Rat::zero())
                .expect("both cells are joinable");
            assert!(closed.residual.values().all(Zero::is_zero));
            assert_eq!(
                name_the_cut(&closed, &load).unwrap().name(),
                "circulation j != 0"
            );

            let open = read_the_chain(&complex, &walk(&[(left, 1)]), Rat::zero())
                .expect("the cell is joinable");
            let cut = name_the_cut(&open, &load).unwrap();
            assert_eq!(cut.name(), "leak");
            let SpineCut::Leak { at } = &cut else {
                panic!("the source and the sink are exhibited");
            };
            assert_eq!(at.len(), 2, "one source and one sink, both named");
        }

        /// A grade-0 address offered where a load **edge** is expected is refused. The two carriers
        /// share one identity space by construction, so this is the check that keeps that safe.
        #[test]
        fn a_vertex_address_is_not_a_load_edge() {
            let (complex, a, left, right) = two_lane();
            let reading = read_the_chain(&complex, &walk(&[(left, 1), (right, -1)]), Rat::zero())
                .expect("both cells are joinable");
            assert_eq!(
                name_the_cut(&reading, &BTreeSet::from([EdgeId(a.0)])),
                Err(SpineCutError::LoadEdgeNotCarried(EdgeId(a.0)))
            );
        }

        /// A cell whose two ends are the same vertex has no tail and head to read, so the chain law
        /// cannot be posed over it. Refused by name rather than approximated.
        #[test]
        fn a_self_incident_cell_is_refused_by_name() {
            let mut complex = GradedCausalComplex::default();
            let a = zero_cell(&mut complex, "a");
            let mut boundary = CausalChain::default();
            boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
            let loop_cell = complex
                .found_cell("loop", source(), 1, boundary)
                .expect("the cell founds");
            assert_eq!(
                read_the_chain(&complex, &CausalChain::default(), Rat::zero()),
                Err(SpineCutError::UnjoinableCell(loop_cell))
            );
        }

        /// A current naming a cell the complex does not carry as a one-cell is refused.
        #[test]
        fn a_current_off_the_incidence_is_refused_by_name() {
            let (complex, a, _, _) = two_lane();
            assert_eq!(
                read_the_chain(&complex, &walk(&[(a, 1)]), Rat::zero()),
                Err(SpineCutError::UnknownEdge(EdgeId(a.0)))
            );
        }
    }

    // --- the counted mouth ------------------------------------------------------------------

    mod counted {
        use super::*;

        fn transfer(id: u64, tail: u64, head: u64, population: Option<i64>) -> CountedTransfer {
            CountedTransfer {
                id: EdgeId(id),
                tail: VertexId(tail),
                head: VertexId(head),
                name: format!("station {tail} -> station {head}"),
                population: population.map(rat),
            }
        }

        /// A counted loop that closes: what one station emits is what the next receives, and the
        /// last returns to the first. The residual is computed from the declared reading, never
        /// supplied.
        #[test]
        fn a_counted_loop_closes_when_the_populations_agree() {
            let reading = read_counted_transfers(
                [
                    transfer(1, 1, 2, Some(223)),
                    transfer(2, 2, 3, Some(223)),
                    transfer(3, 3, 1, Some(223)),
                ],
                rat(0),
            )
            .expect("every population is carried");
            assert!(reading.residual.values().all(Zero::is_zero));
            let cut = name_the_cut(&reading, &BTreeSet::from([EdgeId(2)])).unwrap();
            assert_eq!(cut.name(), "circulation j != 0");

            // And a station that does not pass on what it received is a leak, named at the vertex.
            let leaking = read_counted_transfers(
                [
                    transfer(1, 1, 2, Some(223)),
                    transfer(2, 2, 3, Some(218)),
                    transfer(3, 3, 1, Some(223)),
                ],
                rat(0),
            )
            .expect("every population is carried");
            let cut = name_the_cut(&leaking, &BTreeSet::from([EdgeId(2)])).unwrap();
            assert_eq!(cut.name(), "leak");
            let SpineCut::Leak { at } = &cut else {
                panic!("the source and the sink are exhibited");
            };
            assert_eq!(at.get(&VertexId(2)), Some(&rat(5)));
        }

        /// **An absent population is refused, never read as zero.** A receipt that does not carry a
        /// figure is not a receipt that carries nothing crossing, and reading the second as the
        /// first is how a chain comes out closed for want of a field.
        #[test]
        fn a_transfer_whose_population_the_material_does_not_carry_is_refused_by_name() {
            let refusal = read_counted_transfers(
                [transfer(1, 1, 2, Some(223)), transfer(2, 2, 1, None)],
                rat(0),
            );
            match refusal {
                Err(SpineCutError::PopulationNotCarried { edge, name }) => {
                    assert_eq!(edge, EdgeId(2));
                    assert_eq!(name, "station 2 -> station 1");
                }
                other => panic!("an absent population must refuse, returned {other:?}"),
            }
        }
    }

    // --- the exterior control: attention sinks ------------------------------------------------

    mod the_sink {
        use super::*;
        use num_bigint::BigInt;

        fn ratio(numerator: i64, denominator: i64) -> Rat {
            Rat::new(BigInt::from(numerator), BigInt::from(denominator))
        }

        fn row(entries: &[(i64, i64)]) -> Vec<Rat> {
            entries
                .iter()
                .map(|(numerator, denominator)| ratio(*numerator, *denominator))
                .collect()
        }

        /// **The nop fixture.** Four positions, the sink at `3`. Every query routes its whole
        /// attention to the sink; the sink is a null token that attends itself and carries no value
        /// mass. `arXiv:2605.08453`: the output is identically zero.
        fn nop() -> AttentionHead {
            let to_sink = row(&[(0, 1), (0, 1), (0, 1), (1, 1)]);
            AttentionHead::declare(
                vec![to_sink.clone(), to_sink.clone(), to_sink.clone(), to_sink],
                vec![
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(0, 1), (1, 1), (0, 1)]),
                    row(&[(0, 1), (0, 1), (1, 1)]),
                    row(&[(0, 1), (0, 1), (0, 1)]),
                ],
                3,
                [0, 1, 2],
            )
            .expect("the fixture is stochastic and meets")
        }

        /// **The broadcast fixture.** The same four positions. The sink aggregates uniformly from
        /// the context — its value **is** the aggregate — and every query reads it back.
        /// `arXiv:2606.08105`: the outputs come out low rank.
        fn broadcast() -> AttentionHead {
            let to_sink = row(&[(0, 1), (0, 1), (0, 1), (1, 1)]);
            let aggregate = row(&[(1, 3), (1, 3), (1, 3), (0, 1)]);
            AttentionHead::declare(
                vec![to_sink.clone(), to_sink.clone(), to_sink, aggregate],
                vec![
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(0, 1), (1, 1), (0, 1)]),
                    row(&[(0, 1), (0, 1), (1, 1)]),
                    row(&[(1, 3), (1, 3), (1, 3)]),
                ],
                3,
                [0, 1, 2],
            )
            .expect("the fixture is stochastic and meets")
        }

        /// **The nop is the rest cut**, and the two diagnostics say so before the chain is built.
        #[test]
        fn a_nop_sink_carries_no_value_mass_returns_a_zero_output_and_is_at_rest() {
            let head = nop();
            let diagnostics = head.diagnose().expect("the head reads");
            assert_eq!(diagnostics.sink_value_mass, rat(0));
            assert_eq!(diagnostics.output_rank, 0);
            assert_eq!(diagnostics.full_rank_bound, 3);
            assert_eq!(
                diagnostics.species(),
                SinkReading::Species(SinkSpecies::Nop)
            );

            let verdict = classify_sink(&head, SinkSpecies::Nop).expect("the label agrees");
            assert_eq!(verdict.cut.name(), "rest");
            assert!(!verdict.cut.returns());
            assert!(verdict.agrees());
        }

        /// **The broadcast is circulation through the hub**: closed, non-zero, and crossing the
        /// delivery load. Every current on the chain passes through position `3`.
        #[test]
        fn a_broadcast_sink_redistributes_a_low_rank_output_and_circulates_through_the_hub() {
            let head = broadcast();
            let diagnostics = head.diagnose().expect("the head reads");
            assert_eq!(diagnostics.sink_value_mass, rat(1));
            assert_eq!(
                diagnostics.output_rank, 1,
                "every query receives one aggregate"
            );
            assert_eq!(diagnostics.full_rank_bound, 3);
            assert_eq!(
                diagnostics.species(),
                SinkReading::Species(SinkSpecies::Broadcast)
            );

            let reading = head.read_the_head().expect("the head reads");
            assert!(
                reading.residual.values().all(Zero::is_zero),
                "the hub returns exactly what it aggregated: {:?}",
                reading.residual
            );
            let verdict = classify_sink(&head, SinkSpecies::Broadcast).expect("the label agrees");
            assert_eq!(verdict.cut.name(), "circulation j != 0");
            assert!(verdict.cut.returns());
            assert!(verdict.agrees());

            // Every carried edge touches the sink. That is what "through a hub" means, and it is
            // exhibited rather than asserted in prose.
            let SpineCut::Circulation { crossed, .. } = &verdict.cut else {
                panic!("the crossing is exhibited");
            };
            assert_eq!(crossed.len(), 3, "one delivery per read position");
            for edge in reading.carrying() {
                let raw = edge.0 as usize;
                let (tail, head_position) = (raw / 4, raw % 4);
                assert!(
                    tail == 3 || head_position == 3,
                    "edge {tail} -> {head_position}"
                );
            }
        }

        /// **The mislabelled control.** The same broadcast head, declared a nop, is refused by name.
        /// A classifier that cannot disagree with its label has classified nothing.
        #[test]
        fn a_head_declared_as_the_wrong_species_is_refused_by_name() {
            assert_eq!(
                classify_sink(&broadcast(), SinkSpecies::Nop),
                Err(SpineCutError::SinkSpeciesRefuted {
                    declared: SinkSpecies::Nop,
                    read: SinkReading::Species(SinkSpecies::Broadcast),
                })
            );
            assert_eq!(
                classify_sink(&nop(), SinkSpecies::Broadcast),
                Err(SpineCutError::SinkSpeciesRefuted {
                    declared: SinkSpecies::Broadcast,
                    read: SinkReading::Species(SinkSpecies::Nop),
                })
            );
        }

        /// **A head that is neither species is named neither.** Three positions each attending
        /// themselves: the output is the value table, its rank is full, and nothing is
        /// redistributed through one position. Without this return the classifier would assign one
        /// of two labels to every head it was ever handed.
        #[test]
        fn a_head_that_routes_content_directly_is_neither_species() {
            let head = AttentionHead::declare(
                vec![
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(0, 1), (1, 1), (0, 1)]),
                    row(&[(0, 1), (0, 1), (1, 1)]),
                ],
                vec![
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(0, 1), (1, 1), (0, 1)]),
                    row(&[(0, 1), (0, 1), (1, 1)]),
                ],
                0,
                [0, 1, 2],
            )
            .expect("the fixture is stochastic and meets");
            let diagnostics = head.diagnose().expect("the head reads");
            assert_eq!(diagnostics.output_rank, 3);
            assert_eq!(diagnostics.full_rank_bound, 3);
            assert!(matches!(diagnostics.species(), SinkReading::Neither { .. }));
            assert!(matches!(
                classify_sink(&head, SinkSpecies::Broadcast),
                Err(SpineCutError::SinkSpeciesRefuted { .. })
            ));
        }

        /// **The two readings can disagree, and this is the head where they do.** The sink's value
        /// carries three times the mass it aggregated — it looks like a broadcast to both published
        /// diagnostics and it is a **leak** on the chain, with the excess named at the hub. That is
        /// the falsifier for the agreement asserted above: the diagnostics never see the chain, so
        /// the agreement in the two fixtures is evidence rather than construction.
        #[test]
        fn a_hub_that_emits_more_than_it_aggregated_reads_as_a_broadcast_and_leaks() {
            let to_sink = row(&[(0, 1), (0, 1), (0, 1), (1, 1)]);
            let aggregate = row(&[(1, 3), (1, 3), (1, 3), (0, 1)]);
            let head = AttentionHead::declare(
                vec![to_sink.clone(), to_sink.clone(), to_sink, aggregate],
                vec![
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(0, 1), (1, 1), (0, 1)]),
                    row(&[(0, 1), (0, 1), (1, 1)]),
                    row(&[(1, 1), (1, 1), (1, 1)]),
                ],
                3,
                [0, 1, 2],
            )
            .expect("the fixture is stochastic and meets");
            let diagnostics = head.diagnose().expect("the head reads");
            assert_eq!(diagnostics.sink_value_mass, rat(3));
            assert_eq!(diagnostics.output_rank, 1);
            assert_eq!(
                diagnostics.species(),
                SinkReading::Species(SinkSpecies::Broadcast),
                "the published diagnostics cannot see the imbalance"
            );

            let verdict = classify_sink(&head, SinkSpecies::Broadcast).expect("the label agrees");
            assert_eq!(verdict.cut.name(), "leak");
            assert!(
                !verdict.agrees(),
                "the chain refuses what the diagnostics accepted"
            );
            let SpineCut::Leak { at } = &verdict.cut else {
                panic!("the source is exhibited");
            };
            assert_eq!(
                at.get(&VertexId(3)),
                Some(&rat(-2)),
                "the hub is the source"
            );
        }

        /// **The short-circuit cut on this material**: a broadcast whose hub never delivers to the
        /// position the caller reads. The loop closes, the current is non-zero, and the load is not
        /// crossed. Position `3` attends only itself, so nothing reaches it.
        #[test]
        fn a_broadcast_that_never_reaches_the_read_position_is_a_short_circuit() {
            let to_sink = row(&[(0, 1), (0, 1), (0, 1), (0, 1), (1, 1)]);
            let apart = row(&[(0, 1), (0, 1), (0, 1), (1, 1), (0, 1)]);
            let aggregate = row(&[(1, 3), (1, 3), (1, 3), (0, 1), (0, 1)]);
            let head = AttentionHead::declare(
                vec![to_sink.clone(), to_sink.clone(), to_sink, apart, aggregate],
                vec![
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(0, 1), (1, 1), (0, 1)]),
                    row(&[(0, 1), (0, 1), (1, 1)]),
                    row(&[(1, 1), (0, 1), (0, 1)]),
                    row(&[(1, 3), (1, 3), (1, 3)]),
                ],
                4,
                [3],
            )
            .expect("the fixture is stochastic and meets");
            let verdict = classify_sink(&head, SinkSpecies::Broadcast).expect("the label agrees");
            assert_eq!(verdict.cut.name(), "short circuit");
            assert!(!verdict.cut.returns());
            assert!(
                verdict.agrees(),
                "a short circuit is still a closed broadcast"
            );
            let SpineCut::ShortCircuit {
                bypass,
                declared_load,
            } = &verdict.cut
            else {
                panic!("the bypass is exhibited");
            };
            assert!(bypass.is_disjoint(declared_load));
        }

        /// The construction refusals. Each is a reading the material could carry and this organ
        /// must not: a row that is not a distribution, a sink outside the head, an undeclared read
        /// set, and tables that do not meet.
        #[test]
        fn a_head_that_is_not_an_attention_map_is_refused_by_name() {
            let values = vec![row(&[(1, 1)]), row(&[(0, 1)])];
            assert!(matches!(
                AttentionHead::declare(
                    vec![row(&[(1, 2), (1, 4)]), row(&[(1, 2), (1, 2)])],
                    values.clone(),
                    0,
                    [0],
                ),
                Err(SpineCutError::AttentionRowIsNotStochastic { query: 0, .. })
            ));
            assert_eq!(
                AttentionHead::declare(
                    vec![row(&[(1, 1), (0, 1)]), row(&[(0, 1), (1, 1)])],
                    values.clone(),
                    9,
                    [0],
                ),
                Err(SpineCutError::PositionOutsideTheHead(9))
            );
            assert_eq!(
                AttentionHead::declare(
                    vec![row(&[(1, 1), (0, 1)]), row(&[(0, 1), (1, 1)])],
                    values,
                    0,
                    [],
                ),
                Err(SpineCutError::ReadPositionsNotDeclared)
            );
            assert_eq!(
                AttentionHead::declare(
                    vec![row(&[(1, 1), (0, 1)]), row(&[(0, 1), (1, 1)])],
                    vec![row(&[(1, 1)])],
                    0,
                    [0],
                ),
                Err(SpineCutError::HeadTablesDoNotMeet {
                    queries: 2,
                    keys: 2,
                    rows: 1
                })
            );
        }
    }
}
