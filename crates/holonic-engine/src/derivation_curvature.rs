//! A derivation has a layout, the layout has curvature, and the curvature is spent back into the
//! geometry that produced it.
//!
//! # What this wires, and to what
//!
//! [`conditioned_derivation`](crate::conditioned_derivation) reads a conditioned body's production
//! as a [`ConditionedCircuit`]: a `GradedCausalComplex` whose 0-cells are the passages, the symbols
//! they recruit and the statements they reach, whose 1-cells are the recruitments and reaches, and
//! whose `provenance` names, for every cell, the passages that founded it. That last map is the
//! whole reason this module can exist: a curvature deficit at an anonymous vertex is not an
//! artifact, and [`ConditionedCircuit::passages_founding`] is what makes every return here carry
//! the passage it sits on.
//!
//! [`curvature_bridge`](crate::curvature_bridge) reads a [`LocalStarStanding`], returns one exact
//! deficit per conducted vertex, applies `discrete_curvature`'s update law, lifts each revised
//! scalar back onto the line the layout carried, and writes the successor response population into
//! the standing. Until now it had exactly one consumer and **its loop had been entered nowhere**:
//! nothing built a standing out of something that was not already a piece of geometry.
//!
//! This module is the join. It is not a second curvature law, not a second lift, and not a second
//! reading of a derivation; it owns exactly two things nobody owned:
//!
//! ```text
//!   the layout       DerivationLayout          the circuit as a hinge incidence, every site and
//!                                              every incidence named by the passages that founded it
//!   the realization  DerivationCurvatureBody   that incidence realized as a closed oriented
//!                                              triangulated surface the bridge can read, plus the
//!                                              write-back into local_star's own geometry
//! ```
//!
//! # The mechanism in the four slots `CLAUDE.md` §4 asks for
//!
//! ```text
//!   source geometry   the conditioned production: which passage recruits which symbol
//!   receiver map      the realization: the derivation's 1-cells declared as the hinge population of
//!                     a closed surface, everything else in that surface refused by name
//!   transport         discrete_curvature's update law -- every vertex discharges its whole deficit
//!                     into its own incidences in equal exact shares
//!   returned residual the deficits that moved and the deficits that did not, each carrying the
//!                     passages that founded the cell it sits on, plus the incidences whose lift the
//!                     bridge refused, deposited whole
//! ```
//!
//! # Coordination is recruitment
//!
//! At unit response `discrete_curvature`'s deficit is exactly `6 - n_v`, and here `n_v` is the
//! number of the derivation's own 1-cells at a site. **A passage recruiting widely sits at a vertex
//! of high coordination and carries a large negative deficit; one recruiting narrowly sits at low
//! coordination and carries a positive one.** That is the whole content of the reading and it needs
//! no interpretation layer.
//!
//! **Grade the deficit, never the combinatorial charge.** The charge is `FLAT_COORDINATION - n_v`
//! and moves only when the circuit changes; a run that graded it would watch the flow move nothing
//! and conclude wrongly. [`NamedDeficit`] carries both so the difference is visible, and
//! [`NamedFlowStep`] grades the deficit.
//!
//! # The realization, and why it needs a scaffold
//!
//! `curvature_bridge`'s declared aperture is the **interior-cycle** vertex subpopulation: a vertex
//! conducts only when its simplicial link is a cycle, which is a statement about *faces*. A
//! derivation circuit is a graph and has no faces, so a realization must supply them. Two things
//! are then true at once and both are load-bearing:
//!
//! - the **hinge** population must be the derivation's own 1-cells and nothing else, because that is
//!   what the deficit counts;
//! - the **face** population is scaffolding, whose only job is to certify that every derivation site
//!   is an interior cycle.
//!
//! The scaffold is built by an explicit construction with no embedding search in it. Order every
//! site's neighbours canonically; that rotation system makes the layout a ribbon graph, whose face
//! permutation `d = (u -> v)  |->  (v -> rho_v(u))` partitions the darts into closed walks. For a
//! walk `v_1 -> v_2 -> ... -> v_k -> v_1` found one fresh **rim** vertex `w_i` per dart and three
//! families of oriented triangles:
//!
//! ```text
//!   T_i = [v_i, v_{i+1}, w_i]        one per dart      -- carries the derivation edge itself
//!   E_i = [w_{i-1}, v_i, w_i]        one per dart      -- the corner at v_i
//!   F_j = [w_1, w_j, w_{j+1}]        j = 2 .. k-1      -- the rim polygon, fanned
//! ```
//!
//! Three facts about it are checked rather than assumed, and each has a test:
//!
//! 1. **Every edge carries exactly two cofaces with opposite hands**, so every edge is a lawful
//!    hinge and the surface is oriented. A derivation edge `{u,v}` has exactly two darts, in
//!    opposite directions, each in exactly one walk position, so it gets `T` from each.
//! 2. **Every site's link is a single cycle of length `3 n_v`.** Per corner the link carries the
//!    path `v_{i-1} - w_{i-1} - w_i - v_{i+1}`; the rim vertices are distinct because there is one
//!    per dart; and the corners chain through the neighbours in the rotation's own cyclic order,
//!    which is a single cycle by construction. **This holds whether or not a face walk repeats a
//!    vertex**, which is why no simplicity condition is imposed on the ribbon graph and no
//!    embedding is searched for.
//! 3. **Every rim vertex's link is a cycle too**, so the scaffold sites are interior cycles that
//!    carry no hinge once the hinge population is narrowed — [`ApertureRefusal::InteriorCycleWithoutHinges`],
//!    a typed refusal, and *not* a leak: no retained hinge touches a rim vertex, so
//!    [`CurvatureAperture::porous_vertices`] is empty and `read` conducts.
//!
//! The narrowing is the documented lifecycle `HingeWorldStanding` states for its own complex
//! (`simplicial.rs:826-828`) and the one `curvature_bridge`'s own fixtures use. It cannot be done at
//! founding: `LocalStarLaw::face_fields` refuses a face boundary edge without a hinge, so every edge
//! is hinged, the standing is founded, and only then is the hinge population narrowed to the
//! derivation's. Both standings are kept — the scaffold one is what `local_star`'s event law
//! advances, the narrowed one is what the bridge reads.
//!
//! # Two frames, and the orbit that proves they are two
//!
//! `CLAUDE.md` §8: a gauge whose group acts trivially is not a gauge, and agreement between frames
//! is evidence only after they have been shown distinct on the declared material.
//!
//! - **Frame D**, the derivation's own: `DiscreteCurvatureConfiguration::at_unit_response` over the
//!   circuit's 1-cells. It never sees a face, a position, a response vector or a projection.
//! - **Frame S**, the surface's: `curvature_bridge::read` over the realized standing, whose scalar
//!   per hinge is `response . edge_vector` and whose link sizes are counted from the complex's hinge
//!   incidence.
//!
//! They are distinct, and [`FrameAgreement::coordination_orbit`] exhibits the orbit rather than
//! asserting it: at **every** conducted site the scaffold's face-derived coordination is exactly
//! `3` times the derivation's own, so `CurvatureBridgeReading::frame_disagreements` is the whole
//! conducted population and not the empty one. On top of that the surface carries `2 |E|` rim
//! vertices the derivation does not have, every one of them refused by name. Against that
//! background the two frames return **the same deficit at every site**, which is a measurement.
//!
//! # The write-back, which is the loop
//!
//! `local_star.rs:2301` clones `geometry_responses` verbatim into the successor standing, so the
//! population that produced the curvature is a constant of the motion. `curvature_bridge::revise_partially`
//! is the deed that breaks that: apply the lift where it is defined, gate on
//! [`PartialCurvatureBridgeStep::is_whole`], and deposit the hinges whose lift is undefined as a
//! population. [`DerivationCurvatureBody::flow`] enters it, and every refusal it deposits is named
//! with the passages that founded the incidence.
//!
//! [`DerivationCurvatureBody::consume_into_geometry`] then closes the circle at the site the design
//! names. `local_star.rs:2082` spends a response as
//! `displacement = geometry_responses[hinge] * (coordinate_change / 2)`, so writing a revised
//! response into the standing and letting `local_star`'s own event law advance it moves the
//! **positions**. The deed enacts the same event twice — once from the standing as founded, once
//! from the standing carrying the consumed curvature — and returns the sites whose realized
//! position differs, each with the passages that founded it. That difference is consumed curvature
//! changing the geometry, measured rather than argued.
//!
//! # What the flow does not do
//!
//! It does not drive deficits to zero and no run here claims it does. The law negates the total
//! deficit at every step and preserves its magnitude exactly, so a charged layout alternates
//! forever. Worse for the naive claim: a **bipartite component with unequal parts sits fixed at
//! nonzero deficit**, and a derivation layout is always bipartite — passages on one side, the
//! symbols and statements they reach on the other. [`DerivationCurvatureBody::found_at_response`]
//! makes that exhibitable: a one-passage three-recruitment layout at response `4` has deficits
//! `-6` and `2` and **every revision exactly zero**, and `forced_component_scale`, which reads no
//! response at all, returns the same `t = 2` the traced deviations show.
//!
//! # Every declared refusal, and what exercises it
//!
//! The only public entry to a layout is a [`ConditionedCircuit`], which `derivation_atlas::found_circuit`
//! builds, so several refusals are **unreachable through it** and are stated that way rather than
//! claimed as exercised. None of them is counted as evidence anywhere.
//!
//! | refusal | reachable | exercised by |
//! |---|---|---|
//! | [`DerivationCurvatureRefusal::IsolatedSites`] | yes | `a_site_no_incidence_meets_is_refused_by_name_rather_than_carried_with_an_undefined_share` |
//! | [`DerivationCurvatureRefusal::EmptyLayout`] | yes | `a_circuit_with_no_incidence_at_all_is_refused_before_anything_is_realized` |
//! | [`DerivationCurvatureRefusal::UnknownIncidence`] | yes | `naming_an_incidence_the_layout_does_not_carry_is_refused` |
//! | [`DerivationCurvatureRefusal::SelfIncidence`] | **no** | `found_circuit` skips a declaration recruiting itself, and a statement key carries `|- `, which no identifier does |
//! | [`DerivationCurvatureRefusal::ParallelIncidence`] | **no** | recruitments are keyed by `(passage, symbol)` and reaches by `(passage, statement)`, both unique, so two 1-cells cannot bound one pair |
//! | [`DerivationCurvatureRefusal::UnreadGrade`] | **no** | `found_circuit` founds grades 0 and 1 and nothing else |
//! | [`DerivationCurvatureRefusal::IncidenceIsNotAnEdge`] | **no** | every 1-cell it founds carries exactly two boundary terms |
//! | [`DerivationCurvatureRefusal::ScaffoldIdentityDrift`] | **no** | a guard on another module's identity allocation, which must fail loudly rather than silently renumber |
//! | [`DerivationCurvatureRefusal::DegenerateRealization`] | **no** | positions are injective and `Edge::new` refuses a collapsed edge, so no realized edge vector is zero |
//!
//! # What this module must not own
//!
//! It does not own the curvature law, the lift, the aperture, the circuit, the conditioning, or a
//! second reading of a Lean artifact. It calls all of them. It owns no float, no tolerance, no
//! threshold and no scalar that governs: the one scalar it declares is the response target every
//! hinge is founded at, which is a *measurement* of what a hinge spends along its own edge and is
//! carried into the return so a reader can see it.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::{integer, rat, Rat, RatVec3};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::algebraic::CausalCellId;
use crate::conditioned_derivation::ConditionedCircuit;
use crate::curvature_bridge::{
    read as read_standing, revise_partially, ApertureRefusal, CurvatureAperture,
    CurvatureBridgeError, CurvatureBridgeReading, OrthogonalHinge,
};
use crate::derivation_atlas::{statement_vertex_key, DerivationIdentity};
use crate::discrete_curvature::{
    CurvatureFixedPoint, DiscreteCurvatureConfiguration, DiscreteCurvatureError,
};
use crate::{
    CpuExecutor, Edge, EventId, ExactEventLaw, HingeId, HingeTrajectory, HingeTransportNetwork,
    HingeUnitSystem, HingeWorldLaw, LocalStarError, LocalStarEvent, LocalStarLaw, LocalStarMaterial,
    LocalStarStanding, QuadraticHingeAction, SimplicialComplex, VertexId,
};

/// The exact ratio between the scaffold's face-derived coordination at a site and the derivation's
/// own coordination there.
///
/// Three, and it is derived rather than chosen: each corner of a site contributes two rim vertices
/// to its link and each neighbour contributes itself, so a site of derivation coordination `n`
/// links to `n` neighbours and `2n` rim vertices. It is stated as a constant because
/// [`FrameAgreement`] checks it at every conducted site, and a realization that drifted from the
/// construction would break the check rather than quietly return a different surface.
pub const SCAFFOLD_LINK_FOLD: usize = 3;

/// The exact scalar every hinge is founded spending along its own edge, unless a caller declares
/// another.
///
/// One, because at unit response `discrete_curvature`'s deficit is exactly the combinatorial charge
/// `FLAT_COORDINATION - n_v` that `local_star.rs:1151` computes, so the founding reading of a
/// derivation layout *is* its recruitment coordination and nothing has been introduced.
pub const UNIT_RESPONSE: i64 = 1;

// -------------------------------------------------------------------------------------------------
// The layout
// -------------------------------------------------------------------------------------------------

/// What a 0-cell of the circuit stands for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SiteKind {
    /// A passage vertex: one declaration the deposit carried or the conditioned body emitted.
    Passage,
    /// A recruited identifier.
    Symbol,
    /// A statement some passage reached, under a founded statement incidence.
    Statement,
}

/// One 0-cell of the circuit, as a site of the layout.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LayoutSite {
    pub vertex: VertexId,
    pub cell: CausalCellId,
    /// The cell's own name: a declaration name, a recruited identifier, or `|- <statement>`.
    pub name: String,
    pub kind: SiteKind,
    /// Every passage that founded this cell, by name, in population order.
    pub passages: Vec<String>,
    /// Whether every passage that founded this cell was emitted rather than deposited.
    pub derived_only: bool,
}

/// One 1-cell of the circuit, as an incidence of the layout.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LayoutIncidence {
    pub hinge: HingeId,
    pub cell: CausalCellId,
    /// The cell's own name: `<passage><-<symbol>` or `<passage>|-<statement>`.
    pub name: String,
    /// The two sites it bounds, ascending.
    pub endpoints: [VertexId; 2],
    pub passages: Vec<String>,
    pub derived_only: bool,
}

/// The conditioned circuit as a hinge incidence, every cell named by the passages that founded it.
///
/// This is a reading of the complex and nothing else: it computes no curvature, realizes no
/// surface, and holds no response.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationLayout {
    pub schema: String,
    sites: BTreeMap<VertexId, LayoutSite>,
    incidences: BTreeMap<HingeId, LayoutIncidence>,
    site_of_cell: BTreeMap<CausalCellId, VertexId>,
}

impl DerivationLayout {
    /// Read a conditioned circuit as a layout.
    ///
    /// Sites take `VertexId(1..)` and incidences `HingeId(1..)` in the complex's own cell order,
    /// which is the order `SimplicialComplex::found_vertex` and `found_hinge` hand out, so a
    /// realization can found them in step and check rather than translate.
    pub fn read(circuit: &ConditionedCircuit) -> Result<Self, DerivationCurvatureRefusal> {
        let complex = circuit.circuit.complex();

        let passage_keys: BTreeSet<String> = circuit
            .passages
            .iter()
            .enumerate()
            .map(|(ordinal, passage)| match circuit.aperture.identity {
                DerivationIdentity::ByDeclaration => passage.derivation.name.clone(),
                DerivationIdentity::ByRoute => {
                    format!("{}#{ordinal}", passage.derivation.name)
                }
            })
            .collect();
        let statement_keys: BTreeSet<String> = circuit
            .passages
            .iter()
            .map(|passage| statement_vertex_key(&passage.derivation.statement))
            .collect();

        let named = |cell: CausalCellId| -> (Vec<String>, bool) {
            let founding = circuit.passages_founding(cell);
            let names = founding
                .iter()
                .map(|passage| passage.derivation.name.clone())
                .collect();
            let derived_only = !founding.is_empty() && founding.iter().all(|carried| carried.is_derived());
            (names, derived_only)
        };

        let mut unread: Vec<String> = Vec::new();
        for cell in complex.cells().values() {
            if cell.grade > 1 {
                unread.push(cell.name.clone());
            }
        }
        if !unread.is_empty() {
            return Err(DerivationCurvatureRefusal::UnreadGrade { cells: unread });
        }

        let mut sites = BTreeMap::new();
        let mut site_of_cell = BTreeMap::new();
        for cell in complex.cells().values().filter(|cell| cell.grade == 0) {
            let vertex = VertexId(sites.len() as u64 + 1);
            let kind = if passage_keys.contains(&cell.name) {
                SiteKind::Passage
            } else if statement_keys.contains(&cell.name) {
                SiteKind::Statement
            } else {
                SiteKind::Symbol
            };
            let (passages, derived_only) = named(cell.id);
            site_of_cell.insert(cell.id, vertex);
            sites.insert(
                vertex,
                LayoutSite {
                    vertex,
                    cell: cell.id,
                    name: cell.name.clone(),
                    kind,
                    passages,
                    derived_only,
                },
            );
        }

        let mut incidences = BTreeMap::new();
        let mut pairs: BTreeMap<[VertexId; 2], String> = BTreeMap::new();
        let mut self_incident = Vec::new();
        let mut parallel = Vec::new();
        for cell in complex.cells().values().filter(|cell| cell.grade == 1) {
            let support = cell.boundary.support();
            if support.len() != 2 {
                return Err(DerivationCurvatureRefusal::IncidenceIsNotAnEdge {
                    name: cell.name.clone(),
                    bounds: support.len(),
                });
            }
            let mut endpoints = [VertexId(0); 2];
            for (slot, bounded) in support.iter().enumerate() {
                endpoints[slot] = *site_of_cell.get(bounded).ok_or_else(|| {
                    DerivationCurvatureRefusal::IncidenceIsNotAnEdge {
                        name: cell.name.clone(),
                        bounds: support.len(),
                    }
                })?;
            }
            endpoints.sort_unstable();
            if endpoints[0] == endpoints[1] {
                self_incident.push(cell.name.clone());
                continue;
            }
            if let Some(carried) = pairs.get(&endpoints) {
                parallel.push(format!("{carried} and {}", cell.name));
                continue;
            }
            pairs.insert(endpoints, cell.name.clone());
            let hinge = HingeId(incidences.len() as u64 + 1);
            let (passages, derived_only) = named(cell.id);
            incidences.insert(
                hinge,
                LayoutIncidence {
                    hinge,
                    cell: cell.id,
                    name: cell.name.clone(),
                    endpoints,
                    passages,
                    derived_only,
                },
            );
        }
        if !self_incident.is_empty() {
            return Err(DerivationCurvatureRefusal::SelfIncidence {
                names: self_incident,
            });
        }
        if !parallel.is_empty() {
            return Err(DerivationCurvatureRefusal::ParallelIncidence { names: parallel });
        }
        if incidences.is_empty() {
            return Err(DerivationCurvatureRefusal::EmptyLayout);
        }

        let mut degrees: BTreeMap<VertexId, usize> = sites.keys().map(|site| (*site, 0)).collect();
        for incidence in incidences.values() {
            for endpoint in incidence.endpoints {
                *degrees.get_mut(&endpoint).expect("an endpoint is a site") += 1;
            }
        }
        let isolated: Vec<String> = degrees
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(vertex, _)| sites[vertex].name.clone())
            .collect();
        if !isolated.is_empty() {
            return Err(DerivationCurvatureRefusal::IsolatedSites { sites: isolated });
        }

        Ok(Self {
            schema: "holonic-engine.derivation-layout.v1".to_owned(),
            sites,
            incidences,
            site_of_cell,
        })
    }

    pub fn sites(&self) -> &BTreeMap<VertexId, LayoutSite> {
        &self.sites
    }

    pub fn incidences(&self) -> &BTreeMap<HingeId, LayoutIncidence> {
        &self.incidences
    }

    pub fn site(&self, vertex: VertexId) -> Option<&LayoutSite> {
        self.sites.get(&vertex)
    }

    pub fn incidence(&self, hinge: HingeId) -> Option<&LayoutIncidence> {
        self.incidences.get(&hinge)
    }

    pub fn site_of_cell(&self, cell: CausalCellId) -> Option<&LayoutSite> {
        self.site_of_cell.get(&cell).and_then(|at| self.sites.get(at))
    }

    /// The derivation's own coordination at a site: how many of the circuit's 1-cells meet it.
    pub fn coordination(&self, vertex: VertexId) -> usize {
        self.incidences
            .values()
            .filter(|incidence| incidence.endpoints.contains(&vertex))
            .count()
    }

    /// The sites of one kind, in population order.
    pub fn of_kind(&self, kind: SiteKind) -> Vec<&LayoutSite> {
        self.sites
            .values()
            .filter(|site| site.kind == kind)
            .collect()
    }

    /// **Frame D.** The layout as a curvature carrier at unit response, read from the circuit's own
    /// incidence and nothing else — no face, no position, no response vector, no projection.
    pub fn configuration(&self) -> Result<DiscreteCurvatureConfiguration, DiscreteCurvatureError> {
        DiscreteCurvatureConfiguration::at_unit_response(
            self.incidences
                .values()
                .map(|incidence| (incidence.hinge, incidence.endpoints)),
        )
    }
}

// -------------------------------------------------------------------------------------------------
// The ribbon graph the scaffold is traced from
// -------------------------------------------------------------------------------------------------

/// The layout with a canonical rotation at every site, and its darts.
struct RibbonGraph {
    neighbours: BTreeMap<VertexId, Vec<VertexId>>,
    slot: BTreeMap<(VertexId, VertexId), usize>,
    darts: Vec<(VertexId, VertexId)>,
    dart_at: BTreeMap<(VertexId, VertexId), usize>,
}

impl RibbonGraph {
    /// The rotation is ascending neighbour order. Any rotation gives a closed oriented surface; this
    /// one is chosen because it is canonical, so the scaffold is a function of the circuit and
    /// carries no hidden choice.
    fn over(layout: &DerivationLayout) -> Self {
        let mut adjacency: BTreeMap<VertexId, BTreeSet<VertexId>> =
            layout.sites.keys().map(|site| (*site, BTreeSet::new())).collect();
        for incidence in layout.incidences.values() {
            let [lower, upper] = incidence.endpoints;
            adjacency.entry(lower).or_default().insert(upper);
            adjacency.entry(upper).or_default().insert(lower);
        }
        let neighbours: BTreeMap<VertexId, Vec<VertexId>> = adjacency
            .into_iter()
            .map(|(site, ring)| (site, ring.into_iter().collect()))
            .collect();
        let mut slot = BTreeMap::new();
        let mut darts = Vec::new();
        let mut dart_at = BTreeMap::new();
        for (site, ring) in &neighbours {
            for (at, neighbour) in ring.iter().enumerate() {
                slot.insert((*site, *neighbour), at);
                dart_at.insert((*site, *neighbour), darts.len());
                darts.push((*site, *neighbour));
            }
        }
        Self {
            neighbours,
            slot,
            darts,
            dart_at,
        }
    }

    /// `d = (u -> v)` is followed in its face by `(v -> rho_v(u))`.
    fn successor(&self, dart: usize) -> usize {
        let (from, into) = self.darts[dart];
        let ring = &self.neighbours[&into];
        let at = self.slot[&(into, from)];
        let next = ring[(at + 1) % ring.len()];
        self.dart_at[&(into, next)]
    }

    /// The face walks, each a list of dart indices in traversal order.
    fn face_walks(&self) -> Vec<Vec<usize>> {
        let mut seen = vec![false; self.darts.len()];
        let mut walks = Vec::new();
        for start in 0..self.darts.len() {
            if seen[start] {
                continue;
            }
            let mut walk = Vec::new();
            let mut here = start;
            while !seen[here] {
                seen[here] = true;
                walk.push(here);
                here = self.successor(here);
            }
            walks.push(walk);
        }
        walks
    }
}

// -------------------------------------------------------------------------------------------------
// Exact geometry helpers
// -------------------------------------------------------------------------------------------------

/// A nonzero vector orthogonal to `vector`. Exact, and defined for every nonzero input.
fn off_edge(vector: &RatVec3) -> Option<RatVec3> {
    [
        RatVec3::from_i64(1, 0, 0),
        RatVec3::from_i64(0, 1, 0),
        RatVec3::from_i64(0, 0, 1),
    ]
    .iter()
    .map(|axis| vector.cross(axis))
    .find(|candidate| !candidate.norm_squared().is_zero())
}

/// A response spending exactly `target` along `edge_vector` and **not parallel to it**.
///
/// The obliqueness is load-bearing, and `curvature_bridge`'s own fixture notes why: with responses
/// parallel to their own edges, "keep the response's line" and "use the edge's line" are the same
/// line, so a lift that substituted the edge as a canonical direction would pass every assertion
/// about direction. The orthogonal summand dots to zero against the edge, so it is invisible to the
/// projection and visible to the lift.
fn response_spending(edge_vector: &RatVec3, target: &Rat) -> Option<RatVec3> {
    let squared = edge_vector.norm_squared();
    if squared.is_zero() {
        return None;
    }
    let along = edge_vector.scale(&(target / &squared));
    Some(along.add(&off_edge(edge_vector)?.scale(&rat(1, 7))))
}

/// A distinct exact position per vertex ordinal, on the smallest cubic lattice that holds them all.
///
/// Nothing geometric is claimed by it. Positions exist because `LocalSpatialStanding` carries one
/// exact vector per edge and the projection reads it; the only property required is that adjacent
/// sites differ, which an injective map guarantees.
fn lattice_position(ordinal: u64, base: u64) -> RatVec3 {
    let x = (ordinal % base) as i64;
    let y = ((ordinal / base) % base) as i64;
    let z = (ordinal / (base * base)) as i64;
    RatVec3::from_i64(x, y, z)
}

fn lattice_base(count: u64) -> u64 {
    let mut base = 2u64;
    while base * base * base <= count {
        base += 1;
    }
    base
}

fn units() -> HingeUnitSystem {
    HingeUnitSystem {
        coordinate: "recruitment".to_owned(),
        event_step: "event".to_owned(),
        action: "action".to_owned(),
        momentum: "action/recruitment".to_owned(),
        impulse: "action/recruitment".to_owned(),
    }
}

// -------------------------------------------------------------------------------------------------
// The realized body
// -------------------------------------------------------------------------------------------------

/// One conducted site with both readings of its coordination and its exact deficit, named by the
/// passages that founded the cell it is.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedDeficit {
    pub vertex: VertexId,
    pub cell: CausalCellId,
    pub name: String,
    pub kind: SiteKind,
    pub derived_only: bool,
    /// The derivation's own coordination: how many 1-cells of the circuit meet this site.
    pub coordination: usize,
    /// The scaffold's face-derived coordination. `SCAFFOLD_LINK_FOLD` times the line above.
    pub scaffold_coordination: usize,
    /// `FLAT_COORDINATION - coordination`. Moves only when the circuit changes; never graded.
    pub combinatorial_charge: i64,
    /// The exact deficit. **This is what is graded.**
    pub deficit: Rat,
    pub passages: Vec<String>,
}

impl NamedDeficit {
    pub fn is_flat(&self) -> bool {
        self.deficit.is_zero()
    }
}

/// One conducted site's deficit read in both frames.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FramePair {
    pub vertex: VertexId,
    pub name: String,
    /// The scaffold's face-derived coordination, from `local_star`'s own link classification.
    pub scaffold_coordination: usize,
    /// The derivation's coordination, counted from hinge incidence.
    pub derivation_coordination: usize,
    /// Frame S: `curvature_bridge::read` over the realized standing.
    pub surface_deficit: Rat,
    /// Frame D: `DiscreteCurvatureConfiguration::at_unit_response` over the circuit's 1-cells.
    pub derivation_deficit: Rat,
}

impl FramePair {
    /// The two frames read this site's coordination differently. Both outcomes have material and
    /// this one is the orbit.
    pub fn coordinations_differ(&self) -> bool {
        self.scaffold_coordination != self.derivation_coordination
    }

    pub fn deficits_agree(&self) -> bool {
        self.surface_deficit == self.derivation_deficit
    }
}

/// The two frames over one layout, with the orbit exhibited before any agreement is read.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameAgreement {
    pub schema: String,
    /// Every conducted site, in both frames.
    pub pairs: Vec<FramePair>,
    /// Sites of the realization that carry no derivation incidence, with the typed reason
    /// `curvature_bridge` refused them. The scaffold, returned as a population.
    pub refused_scaffold: Vec<String>,
}

impl FrameAgreement {
    /// **The orbit.** Conducted sites whose two coordinations differ. Empty means the realization
    /// added nothing the derivation did not already carry, and then agreement below is a tautology.
    pub fn coordination_orbit(&self) -> Vec<&FramePair> {
        self.pairs
            .iter()
            .filter(|pair| pair.coordinations_differ())
            .collect()
    }

    /// Conducted sites at which the two frames returned different deficits. Must be empty.
    pub fn deficit_disagreements(&self) -> Vec<&FramePair> {
        self.pairs
            .iter()
            .filter(|pair| !pair.deficits_agree())
            .collect()
    }

    /// The construction's own law: the scaffold link is exactly `SCAFFOLD_LINK_FOLD` times the
    /// derivation's coordination at every conducted site.
    pub fn fold_holds(&self) -> bool {
        self.pairs.iter().all(|pair| {
            pair.scaffold_coordination == SCAFFOLD_LINK_FOLD * pair.derivation_coordination
        })
    }

    /// The gauge acted, and under it the deficits agree. Both halves, in that order.
    pub fn acts_nontrivially_and_agrees(&self) -> bool {
        !self.coordination_orbit().is_empty() && self.deficit_disagreements().is_empty()
    }
}

/// One site whose deficit was read before and after a flow step.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MovedDeficit {
    pub vertex: VertexId,
    pub name: String,
    pub kind: SiteKind,
    pub before: Rat,
    pub after: Rat,
    pub passages: Vec<String>,
}

impl MovedDeficit {
    pub fn moved(&self) -> bool {
        self.before != self.after
    }
}

/// One incidence whose response the lift revised, named by the passages that founded it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RevisedIncidence {
    pub hinge: HingeId,
    pub name: String,
    pub passages: Vec<String>,
    pub spent_before: Rat,
    pub spent_after: Rat,
    /// `spent_after / spent_before`. The lift keeps the response's line verbatim and revises only
    /// the magnitude, and its sense when this is negative.
    pub magnitude_factor: Rat,
}

/// One incidence whose lift the bridge refused, deposited whole.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnliftedIncidence {
    pub hinge: HingeId,
    pub name: String,
    pub passages: Vec<String>,
    pub refusal: OrthogonalHinge,
}

/// One application of the curvature law to a derivation layout, with everything named.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedFlowStep {
    pub ordinal: usize,
    /// Sites whose deficit changed.
    pub moved: Vec<MovedDeficit>,
    /// Sites whose deficit did not.
    pub still: Vec<MovedDeficit>,
    pub revised: Vec<RevisedIncidence>,
    /// The population the partial arm deposited. Empty is a report, not a silence.
    pub unlifted: Vec<UnliftedIncidence>,
    pub total_before: Rat,
    pub total_after: Rat,
    /// Whether the whole conducted hinge population was lifted. The boolean the design permits a
    /// caller to gate on; the population is [`Self::unlifted`].
    pub whole: bool,
}

impl NamedFlowStep {
    /// The step moved at least one deficit.
    pub fn moved_something(&self) -> bool {
        !self.moved.is_empty()
    }

    /// `discrete_curvature` Consequence 2: the total deficit is negated exactly.
    pub fn total_is_negated(&self) -> bool {
        self.total_after == -self.total_before.clone()
    }
}

/// One site whose realized position moved because the standing consumed its own curvature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DisplacedSite {
    pub vertex: VertexId,
    pub name: String,
    pub kind: SiteKind,
    pub passages: Vec<String>,
    /// The position `local_star`'s event law returns from the standing as founded.
    pub without_consumption: RatVec3,
    /// The position it returns from the standing carrying the consumed curvature.
    pub with_consumption: RatVec3,
    pub difference: RatVec3,
}

/// What consuming the curvature did to the geometry, measured through `local_star`'s own event law.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeometryConsumption {
    pub schema: String,
    /// The incidence the event drove.
    pub hinge: HingeId,
    pub incidence: String,
    pub passages: Vec<String>,
    pub source_current: Rat,
    /// The response that incidence carried, before and after the write-back.
    pub response_before: RatVec3,
    pub response_after: RatVec3,
    /// Every site whose realized position differs between the two enactments.
    pub displaced: Vec<DisplacedSite>,
}

impl GeometryConsumption {
    /// The write-back reached the geometry.
    pub fn moved_the_geometry(&self) -> bool {
        !self.displaced.is_empty()
    }
}

/// A derivation layout realized as a standing the bridge reads, with the write-back attached.
#[derive(Clone, Debug)]
pub struct DerivationCurvatureBody {
    pub layout: DerivationLayout,
    law: LocalStarLaw,
    /// Every edge of the realization hinged. What `local_star`'s event law advances.
    scaffold: LocalStarStanding,
    /// The same standing with the hinge population narrowed to the derivation's own incidences.
    /// What the bridge reads.
    standing: LocalStarStanding,
    /// The response population as founded, before any consumption.
    pristine: BTreeMap<HingeId, RatVec3>,
    /// Rim vertices: sites of the realization the derivation does not carry.
    rim: BTreeSet<VertexId>,
    face_walks: usize,
    target: Rat,
}

impl DerivationCurvatureBody {
    /// Realize a conditioned circuit at unit response.
    pub fn found(circuit: &ConditionedCircuit) -> Result<Self, DerivationCurvatureRefusal> {
        Self::found_at_response(circuit, integer(UNIT_RESPONSE))
    }

    /// Realize a conditioned circuit with every incidence spending `target` along its own edge.
    ///
    /// The target is a **measurement declared by the caller**, not a governor: it is what each hinge
    /// reports, and the deficit is `FLAT_COORDINATION` minus the sum of the reports at a site. At
    /// `UNIT_RESPONSE` the deficit is the combinatorial charge exactly; at other values it is the
    /// metric refinement of it, which is how a fixed point at nonzero deficit becomes exhibitable.
    pub fn found_at_response(
        circuit: &ConditionedCircuit,
        target: Rat,
    ) -> Result<Self, DerivationCurvatureRefusal> {
        let layout = DerivationLayout::read(circuit)?;
        Self::realize(layout, target)
    }

    /// Realize an already-read layout.
    pub fn realize(
        layout: DerivationLayout,
        target: Rat,
    ) -> Result<Self, DerivationCurvatureRefusal> {
        let ribbon = RibbonGraph::over(&layout);
        let walks = ribbon.face_walks();

        let mut complex = SimplicialComplex::default();
        let founding = EventId(1);

        // The derivation's own sites first, so a site's `VertexId` is the complex's.
        for site in layout.sites.values() {
            let founded = complex.found_vertex(site.name.clone(), founding);
            if founded != site.vertex {
                return Err(DerivationCurvatureRefusal::ScaffoldIdentityDrift {
                    declared: format!("{:?} for {}", site.vertex, site.name),
                    founded: format!("{founded:?}"),
                });
            }
        }
        // Then one rim vertex per dart.
        let mut rim = BTreeSet::new();
        let mut rim_of_dart: Vec<VertexId> = Vec::with_capacity(ribbon.darts.len());
        for (from, into) in &ribbon.darts {
            let name = format!(
                "rim {} -> {}",
                layout.sites[from].name, layout.sites[into].name
            );
            let founded = complex.found_vertex(name, founding);
            rim.insert(founded);
            rim_of_dart.push(founded);
        }

        // The scaffold faces.
        for (walk_at, walk) in walks.iter().enumerate() {
            let span = walk.len();
            let site = |offset: usize| ribbon.darts[walk[offset % span]].0;
            let rim_vertex = |offset: usize| rim_of_dart[walk[offset % span]];
            for position in 0..span {
                complex
                    .found_face(
                        format!("walk-{walk_at} carry-{position}"),
                        founding,
                        [site(position), site(position + 1), rim_vertex(position)],
                    )
                    .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
                complex
                    .found_face(
                        format!("walk-{walk_at} corner-{position}"),
                        founding,
                        [
                            rim_vertex(position + span - 1),
                            site(position),
                            rim_vertex(position),
                        ],
                    )
                    .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
            }
            for fan in 1..span.saturating_sub(1) {
                complex
                    .found_face(
                        format!("walk-{walk_at} rim-{fan}"),
                        founding,
                        [rim_vertex(0), rim_vertex(fan), rim_vertex(fan + 1)],
                    )
                    .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
            }
        }

        // The derivation's own incidences first, so an incidence's `HingeId` is the complex's.
        for incidence in layout.incidences.values() {
            let edge = Edge::new(incidence.endpoints[0], incidence.endpoints[1])
                .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
            let founded = complex
                .found_hinge(incidence.name.clone(), founding, edge)
                .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
            if founded != incidence.hinge {
                return Err(DerivationCurvatureRefusal::ScaffoldIdentityDrift {
                    declared: format!("{:?} for {}", incidence.hinge, incidence.name),
                    founded: format!("{founded:?}"),
                });
            }
        }
        let layout_hinges: BTreeSet<HingeId> = layout.incidences.keys().copied().collect();
        let scaffold_edges: BTreeSet<Edge> = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect();
        let already: BTreeSet<Edge> = complex.hinges.values().map(|hinge| hinge.edge).collect();
        for edge in scaffold_edges.difference(&already) {
            complex
                .found_hinge("scaffold", founding, *edge)
                .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
        }

        // Positions, materials, and the standing.
        let base = lattice_base(complex.vertices.len() as u64 + 1);
        let positions: BTreeMap<VertexId, RatVec3> = complex
            .vertices
            .keys()
            .map(|vertex| (*vertex, lattice_position(vertex.0, base)))
            .collect();

        let mut materials = BTreeMap::new();
        for hinge in complex.hinges.values() {
            let vector = positions[&hinge.edge.upper].subtract(&positions[&hinge.edge.lower]);
            let geometry_response = response_spending(&vector, &target).ok_or(
                DerivationCurvatureRefusal::DegenerateRealization { hinge: hinge.id },
            )?;
            materials.insert(
                hinge.id,
                LocalStarMaterial {
                    action: QuadraticHingeAction::new(integer(2), integer(1), units())
                        .map_err(|error| DerivationCurvatureRefusal::Physical(error.to_string()))?,
                    stress_response: rat(1, 4),
                    geometry_response,
                },
            );
        }

        let parameters: BTreeMap<HingeId, Rat> = complex
            .hinges
            .keys()
            .map(|hinge| (*hinge, integer(0)))
            .collect();
        let trajectories: BTreeMap<HingeId, HingeTrajectory> = complex
            .hinges
            .keys()
            .map(|hinge| {
                (
                    *hinge,
                    HingeTrajectory {
                        previous: integer(0),
                        current: integer(0),
                    },
                )
            })
            .collect();

        let kinematic = HingeWorldLaw::new(complex, HingeTransportNetwork::default(), Vec::new())
            .map_err(|error| DerivationCurvatureRefusal::HingeWorld(error.to_string()))?;
        let kinematic_standing = kinematic
            .initial_standing(parameters)
            .map_err(|error| DerivationCurvatureRefusal::HingeWorld(error.to_string()))?;
        let law = LocalStarLaw::new(kinematic, materials, Vec::new(), CpuExecutor::serial())?;
        let scaffold = law.initial_standing(kinematic_standing, trajectories, positions, Vec::new())?;

        let pristine = scaffold.geometry_responses.clone();
        let mut standing = scaffold.clone();
        standing
            .kinematic
            .complex
            .hinges
            .retain(|hinge, _| layout_hinges.contains(hinge));

        Ok(Self {
            layout,
            law,
            scaffold,
            standing,
            pristine,
            rim,
            face_walks: walks.len(),
            target,
        })
    }

    /// The standing the bridge reads: hinges narrowed to the derivation's own incidences.
    pub fn standing(&self) -> &LocalStarStanding {
        &self.standing
    }

    /// The standing `local_star`'s event law advances: every edge of the realization hinged.
    pub fn scaffold(&self) -> &LocalStarStanding {
        &self.scaffold
    }

    /// The rim vertices the realization added. Every one of them is refused by the aperture.
    pub fn rim(&self) -> &BTreeSet<VertexId> {
        &self.rim
    }

    /// How many face walks the ribbon graph traced.
    pub fn face_walks(&self) -> usize {
        self.face_walks
    }

    /// The response target every incidence was founded spending along its own edge.
    pub fn target(&self) -> &Rat {
        &self.target
    }

    /// **Frame S.** The layout read through `curvature_bridge`.
    pub fn reading(&self) -> Result<CurvatureBridgeReading, DerivationCurvatureRefusal> {
        Ok(read_standing(&self.standing)?)
    }

    /// Every conducted site's deficit, named by the passages that founded the cell it is.
    pub fn named_deficits(
        &self,
        reading: &CurvatureBridgeReading,
    ) -> Vec<NamedDeficit> {
        reading
            .aperture
            .conducted
            .values()
            .filter_map(|conducted| {
                let site = self.layout.site(conducted.vertex)?;
                let deficit = reading.deficits().get(&conducted.vertex).cloned()?;
                Some(NamedDeficit {
                    vertex: site.vertex,
                    cell: site.cell,
                    name: site.name.clone(),
                    kind: site.kind,
                    derived_only: site.derived_only,
                    coordination: conducted.incident_hinges,
                    scaffold_coordination: conducted.link_coordination,
                    combinatorial_charge: conducted.hinge_charge,
                    deficit,
                    passages: site.passages.clone(),
                })
            })
            .collect()
    }

    /// The two frames, with the orbit exhibited before any agreement is read.
    ///
    /// **Frame D is the layout at unit response and nothing else**, because that is the reading in
    /// which `discrete_curvature`'s deficit is the circuit's own recruitment coordination. A body
    /// founded at another response is therefore *expected* to disagree with it, and
    /// `the_derivations_own_frame_is_computed_without_the_standing` uses exactly that to prove the
    /// second frame is a second computation rather than the first one wearing another name.
    pub fn frame_agreement(&self) -> Result<FrameAgreement, DerivationCurvatureRefusal> {
        let reading = self.reading()?;
        let surface = reading.deficits();
        let derivation = self.layout.configuration()?.deficits();
        let pairs = reading
            .aperture
            .conducted
            .values()
            .filter_map(|conducted| {
                let site = self.layout.site(conducted.vertex)?;
                Some(FramePair {
                    vertex: site.vertex,
                    name: site.name.clone(),
                    scaffold_coordination: conducted.link_coordination,
                    derivation_coordination: conducted.incident_hinges,
                    surface_deficit: surface.get(&conducted.vertex).cloned()?,
                    derivation_deficit: derivation.get(&conducted.vertex).cloned()?,
                })
            })
            .collect();
        let refused_scaffold = reading
            .aperture
            .refused
            .iter()
            .map(|(vertex, refusal)| {
                let name = self
                    .standing
                    .kinematic
                    .complex
                    .vertices
                    .get(vertex)
                    .map_or_else(|| format!("{vertex:?}"), |carried| carried.name.clone());
                format!("{name}  {}", refusal_name(*refusal))
            })
            .collect();
        Ok(FrameAgreement {
            schema: "holonic-engine.derivation-frame-agreement.v1".to_owned(),
            pairs,
            refused_scaffold,
        })
    }

    /// The fixed-point class the carrier assigns this layout, read without moving it.
    pub fn fixed_point(&self) -> Result<CurvatureFixedPoint, DerivationCurvatureRefusal> {
        Ok(self.reading()?.configuration.fixed_point())
    }

    /// The scale a bipartite component's traced deviation is forced to, computed from the
    /// bipartition alone. Keyed by each component's least site.
    pub fn forced_component_scale(
        &self,
    ) -> Result<BTreeMap<VertexId, Rat>, DerivationCurvatureRefusal> {
        Ok(self.reading()?.configuration.forced_component_scale())
    }

    /// **Enter the loop.** Apply the curvature law `steps` times, lifting every incidence whose lift
    /// is defined, depositing every one whose lift is not, and writing the successor responses into
    /// the standing each time.
    pub fn flow(&mut self, steps: usize) -> Result<Vec<NamedFlowStep>, DerivationCurvatureRefusal> {
        let mut walked = Vec::with_capacity(steps);
        for ordinal in 1..=steps {
            let applied = revise_partially(&mut self.standing)?;
            let mut moved = Vec::new();
            let mut still = Vec::new();
            for (vertex, before) in &applied.flow.deficits_before {
                let Some(site) = self.layout.site(*vertex) else {
                    continue;
                };
                let after = applied.flow.deficits_after[vertex].clone();
                let entry = MovedDeficit {
                    vertex: *vertex,
                    name: site.name.clone(),
                    kind: site.kind,
                    before: before.clone(),
                    after,
                    passages: site.passages.clone(),
                };
                if entry.moved() {
                    moved.push(entry);
                } else {
                    still.push(entry);
                }
            }
            let revised = applied
                .revisions
                .values()
                .filter_map(|revision| {
                    let incidence = self.layout.incidence(revision.hinge)?;
                    Some(RevisedIncidence {
                        hinge: revision.hinge,
                        name: incidence.name.clone(),
                        passages: incidence.passages.clone(),
                        spent_before: revision.along_edge_before.clone(),
                        spent_after: revision.along_edge_after.clone(),
                        magnitude_factor: revision.magnitude_factor.clone(),
                    })
                })
                .collect();
            let unlifted = applied
                .unlifted
                .values()
                .filter_map(|refusal| {
                    let incidence = self.layout.incidence(refusal.hinge)?;
                    Some(UnliftedIncidence {
                        hinge: refusal.hinge,
                        name: incidence.name.clone(),
                        passages: incidence.passages.clone(),
                        refusal: refusal.clone(),
                    })
                })
                .collect();
            walked.push(NamedFlowStep {
                ordinal,
                moved,
                still,
                revised,
                unlifted,
                total_before: applied.flow.total_deficit_before.clone(),
                total_after: applied.flow.total_deficit_after.clone(),
                whole: applied.is_whole(),
            });
        }
        Ok(walked)
    }

    /// The response population the standing carries now, after whatever has been consumed.
    pub fn consumed_responses(&self) -> &BTreeMap<HingeId, RatVec3> {
        &self.standing.geometry_responses
    }

    /// The response population as founded.
    pub fn pristine_responses(&self) -> &BTreeMap<HingeId, RatVec3> {
        &self.pristine
    }

    /// Incidences whose response the consumption changed, named by their passages.
    pub fn consumption_population(&self) -> Vec<&LayoutIncidence> {
        self.layout
            .incidences
            .values()
            .filter(|incidence| {
                self.standing.geometry_responses.get(&incidence.hinge)
                    != self.pristine.get(&incidence.hinge)
            })
            .collect()
    }

    /// **Close the circle.** Drive one incidence with a source current through `local_star`'s own
    /// event law, twice: once from the standing as founded and once from the standing carrying the
    /// curvature it consumed, and return the sites whose realized position differs.
    ///
    /// `local_star.rs:2082` spends a response as
    /// `displacement = geometry_responses[hinge] * (coordinate_change / 2)`, so this measures the
    /// only thing the write-back can change, through the owner that changes it. Nothing here
    /// re-implements that law.
    pub fn consume_into_geometry(
        &self,
        hinge: HingeId,
        source_current: Rat,
    ) -> Result<GeometryConsumption, DerivationCurvatureRefusal> {
        let incidence = self
            .layout
            .incidence(hinge)
            .ok_or(DerivationCurvatureRefusal::UnknownIncidence(hinge))?;
        let event = LocalStarEvent {
            event: EventId(2),
            source_currents: BTreeMap::from([(hinge, source_current.clone())]),
            receiver_deeds: Vec::new(),
            receiver_population: Vec::new(),
            topology_deeds: Vec::new(),
        };

        let mut consumed = self.scaffold.clone();
        consumed.geometry_responses = self.standing.geometry_responses.clone();

        let without = self.law.enact(&self.scaffold, &event)?;
        let with = self.law.enact(&consumed, &event)?;
        let before = without.standing_after.realized_vertices()?;
        let after = with.standing_after.realized_vertices()?;

        let mut displaced = Vec::new();
        for (vertex, carried) in &before {
            let there = &after[vertex].position;
            let difference = there.subtract(&carried.position);
            if difference.norm_squared().is_zero() {
                continue;
            }
            let (name, kind, passages) = match self.layout.site(*vertex) {
                Some(site) => (site.name.clone(), site.kind, site.passages.clone()),
                None => (
                    self.scaffold
                        .kinematic
                        .complex
                        .vertices
                        .get(vertex)
                        .map_or_else(|| format!("{vertex:?}"), |found| found.name.clone()),
                    SiteKind::Symbol,
                    Vec::new(),
                ),
            };
            displaced.push(DisplacedSite {
                vertex: *vertex,
                name,
                kind,
                passages,
                without_consumption: carried.position.clone(),
                with_consumption: there.clone(),
                difference,
            });
        }

        Ok(GeometryConsumption {
            schema: "holonic-engine.derivation-geometry-consumption.v1".to_owned(),
            hinge,
            incidence: incidence.name.clone(),
            passages: incidence.passages.clone(),
            source_current,
            response_before: self.pristine[&hinge].clone(),
            response_after: self.standing.geometry_responses[&hinge].clone(),
            displaced,
        })
    }

    /// **The declared foil.** Turn one incidence's response orthogonal to its own edge, keeping its
    /// magnitude, so it spends exactly nothing along the edge it is.
    ///
    /// This is not an invention: it is the defect `local_star`'s own octahedral fixture carries —
    /// hinge 10 there holds the response `(1,0,0)` while its edge carries `(0,-3,-4)` — reproduced
    /// on a derivation layout so the partial arm's refusal population has something in it that the
    /// law can be watched refusing. Returns the incidence it moved.
    pub fn refuse_one_lift(
        &mut self,
        hinge: HingeId,
    ) -> Result<LayoutIncidence, DerivationCurvatureRefusal> {
        let incidence = self
            .layout
            .incidence(hinge)
            .ok_or(DerivationCurvatureRefusal::UnknownIncidence(hinge))?
            .clone();
        let edge = Edge::new(incidence.endpoints[0], incidence.endpoints[1])
            .map_err(|error| DerivationCurvatureRefusal::Simplicial(error.to_string()))?;
        let vector = self
            .standing
            .spatial
            .edges
            .get(&edge)
            .ok_or(LocalStarError::MissingSpatialEdge(edge))?
            .vector
            .clone();
        let orthogonal = off_edge(&vector)
            .ok_or(DerivationCurvatureRefusal::DegenerateRealization { hinge })?;
        self.standing
            .geometry_responses
            .insert(hinge, orthogonal.clone());
        self.scaffold.geometry_responses.insert(hinge, orthogonal);
        self.pristine
            .insert(hinge, self.scaffold.geometry_responses[&hinge].clone());
        Ok(incidence)
    }
}

fn refusal_name(refusal: ApertureRefusal) -> &'static str {
    match refusal {
        ApertureRefusal::BoundaryPath { .. } => "boundary path",
        ApertureRefusal::SingularLink { .. } => "singular link",
        ApertureRefusal::IsolatedLink => "isolated link",
        ApertureRefusal::InteriorCycleWithoutHinges => "interior cycle carrying no incidence",
    }
}

/// The aperture a reading declared, handed back so a caller can print the scaffold's refusals.
pub fn declared_aperture(reading: &CurvatureBridgeReading) -> &CurvatureAperture {
    &reading.aperture
}

// -------------------------------------------------------------------------------------------------
// Refusals
// -------------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum DerivationCurvatureRefusal {
    #[error(
        "the circuit carries cells above grade one, which a hinge incidence cannot hold without \
         losing them: {cells:?}"
    )]
    UnreadGrade { cells: Vec<String> },
    #[error("the incidence {name} bounds {bounds} zero-cells rather than two")]
    IncidenceIsNotAnEdge { name: String, bounds: usize },
    #[error(
        "these zero-cells carry no incidence at all, so their traced deviation is undefined and \
         their deficit could never be discharged: {sites:?}"
    )]
    IsolatedSites { sites: Vec<String> },
    #[error("these incidences join one zero-cell to itself: {names:?}")]
    SelfIncidence { names: Vec<String> },
    #[error(
        "these zero-cell pairs carry more than one incidence, which one simplicial edge cannot \
         hinge twice: {names:?}"
    )]
    ParallelIncidence { names: Vec<String> },
    #[error("the layout carries no incidence at all")]
    EmptyLayout,
    #[error(
        "the realization founded {founded} where the layout had declared {declared}, so a site's \
         name and its curvature would belong to different things"
    )]
    ScaffoldIdentityDrift { declared: String, founded: String },
    #[error(
        "hinge {hinge:?} of the realization has a degenerate edge, so no response can be built to \
         spend a declared scalar along it"
    )]
    DegenerateRealization { hinge: HingeId },
    #[error("the layout carries no incidence {0:?}")]
    UnknownIncidence(HingeId),
    #[error("the simplicial complex refused the realization: {0}")]
    Simplicial(String),
    #[error("the kinematic world refused the realization: {0}")]
    HingeWorld(String),
    #[error("the constitutive material refused the realization: {0}")]
    Physical(String),
    #[error("the local-star law refused: {0}")]
    LocalStar(#[from] LocalStarError),
    #[error("the curvature bridge refused: {0}")]
    Bridge(#[from] CurvatureBridgeError),
    #[error("the curvature carrier refused: {0}")]
    Carrier(#[from] DiscreteCurvatureError),
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::conditioned_derivation::{ConditionedBody, DerivationQuery};
    use crate::derivation_atlas::CircuitAperture;

    // ---------------------------------------------------------------------------------------------
    // Material. Three tiny deposits, each of a shape whose curvature is decidable by hand, so the
    // organ's returns can be checked against arithmetic rather than against itself.
    //
    // `read_derivation` drops single-character tokens, so a statement written `: P` recruits
    // nothing and each artifact recruits exactly the identifiers on the right of its `have`s.
    // ---------------------------------------------------------------------------------------------

    /// Two declarations recruiting the same two identifiers. The layout is a four-cycle: every site
    /// of coordination two, bipartite with equal parts, so the forced scale is zero and flat is the
    /// only fixed configuration.
    fn four_cycle_deposit() -> Vec<(String, String)> {
        vec![
            (
                "alpha".to_owned(),
                "theorem alpha : P := by\n  have one := carryOne\n  have two := carryTwo\n"
                    .to_owned(),
            ),
            (
                "beta".to_owned(),
                "theorem beta : P := by\n  have one := carryOne\n  have two := carryTwo\n".to_owned(),
            ),
        ]
    }

    /// One declaration recruiting three identifiers. The layout is a star: bipartite with parts of
    /// size three and one, which is where the nonflat fixed point lives.
    fn star_deposit() -> Vec<(String, String)> {
        vec![(
            "star".to_owned(),
            "theorem star : P := by\n  have one := carryOne\n  have two := carryTwo\n  \
             have three := carryThree\n"
                .to_owned(),
        )]
    }

    /// A statement-blind aperture, so the layout is exactly the recruitment graph.
    fn aperture() -> CircuitAperture {
        CircuitAperture::DEPOSITED_READER
    }

    fn circuit(deposit: Vec<(String, String)>) -> ConditionedCircuit {
        let body = ConditionedBody::mount(deposit).expect("the deposit reads");
        body.circuit(&DerivationQuery::reaching(": P"), aperture())
            .expect("the circuit founds")
    }

    fn four_cycle() -> ConditionedCircuit {
        circuit(four_cycle_deposit())
    }

    fn star() -> ConditionedCircuit {
        circuit(star_deposit())
    }

    fn named(layout: &DerivationLayout, name: &str) -> VertexId {
        layout
            .sites()
            .values()
            .find(|site| site.name == name)
            .unwrap_or_else(|| panic!("the fixture carries a site named {name}"))
            .vertex
    }

    // ---------------------------------------------------------------------------------------------
    // The layout
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn the_layout_is_the_circuit_and_every_site_carries_the_passages_that_founded_it() {
        let circuit = four_cycle();
        let layout = DerivationLayout::read(&circuit).expect("the circuit is a layout");

        assert_eq!(layout.sites().len(), 4, "{:?}", layout.sites());
        assert_eq!(layout.incidences().len(), 4);

        let alpha = named(&layout, "alpha");
        assert_eq!(layout.site(alpha).expect("carried").kind, SiteKind::Passage);
        assert_eq!(
            layout.site(alpha).expect("carried").passages,
            vec!["alpha".to_owned()]
        );
        let carry = named(&layout, "carryOne");
        assert_eq!(layout.site(carry).expect("carried").kind, SiteKind::Symbol);
        // A symbol both declarations recruit is founded by both, and the deficit that lands on it
        // must say so rather than name one.
        assert_eq!(
            layout.site(carry).expect("carried").passages,
            vec!["alpha".to_owned(), "beta".to_owned()]
        );
        for site in layout.sites().values() {
            assert_eq!(layout.coordination(site.vertex), 2, "{}", site.name);
        }
        for incidence in layout.incidences().values() {
            assert!(
                !incidence.passages.is_empty(),
                "an anonymous incidence: {}",
                incidence.name
            );
        }
    }

    #[test]
    fn a_site_no_incidence_meets_is_refused_by_name_rather_than_carried_with_an_undefined_share() {
        // `read_derivation` recruits nothing from `theorem lonely : P := by`, so the declaration's
        // 0-cell stands alone. A vertex of zero coordination has `K(v)/n_v` undefined.
        let body = ConditionedBody::mount(vec![
            (
                "lonely".to_owned(),
                "theorem lonely : P := by\n  have nothing := Q\n".to_owned(),
            ),
            (
                "joined".to_owned(),
                "theorem joined : P := by\n  have one := carryOne\n  have two := carryTwo\n"
                    .to_owned(),
            ),
        ])
        .expect("the deposit reads");
        let circuit = body
            .circuit(&DerivationQuery::reaching(": P"), aperture())
            .expect("the circuit founds");
        // `Q` is a single character and is dropped by the reading, so `lonely` recruits nothing.
        let refusal = DerivationLayout::read(&circuit).expect_err("an isolated site is refused");
        match refusal {
            DerivationCurvatureRefusal::IsolatedSites { sites } => {
                assert_eq!(sites, vec!["lonely".to_owned()]);
            }
            other => panic!("{other}"),
        }
    }

    #[test]
    fn a_circuit_with_no_incidence_at_all_is_refused_before_anything_is_realized() {
        // One declaration that recruits nothing and reaches no founded statement. There is a
        // 0-cell and no 1-cell, so there is no hinge incidence to carry curvature on.
        let body = ConditionedBody::mount(vec![(
            "alone".to_owned(),
            "theorem alone : P := by\n  have x := Q\n".to_owned(),
        )])
        .expect("the deposit reads");
        let circuit = body
            .circuit(&DerivationQuery::reaching(": P"), aperture())
            .expect("the circuit founds");
        assert_eq!(
            DerivationLayout::read(&circuit),
            Err(DerivationCurvatureRefusal::EmptyLayout)
        );
    }

    #[test]
    fn naming_an_incidence_the_layout_does_not_carry_is_refused() {
        let mut body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let absent = HingeId(9_999);
        assert_eq!(
            body.consume_into_geometry(absent, integer(1)).unwrap_err(),
            DerivationCurvatureRefusal::UnknownIncidence(absent)
        );
        assert_eq!(
            body.refuse_one_lift(absent).unwrap_err(),
            DerivationCurvatureRefusal::UnknownIncidence(absent)
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The realization
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn the_realization_is_a_closed_oriented_surface_whose_every_site_is_an_interior_cycle() {
        let body = DerivationCurvatureBody::found(&four_cycle()).expect("the layout realizes");
        let complex = &body.scaffold().kinematic.complex;

        // Every edge of the realization carries a hinge, which `found_hinge` grants only to an edge
        // with exactly two cofaces of opposite hand. That is the closed-and-oriented condition, and
        // it is certified by the founding rather than asserted here.
        let edges: BTreeSet<Edge> = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect();
        assert_eq!(edges.len(), complex.hinges.len());

        // Euler characteristic of a closed surface built from 4 sites, 4 incidences and one rim
        // vertex per dart.
        let darts = 2 * body.layout.incidences().len();
        assert_eq!(complex.vertices.len(), body.layout.sites().len() + darts);
        assert_eq!(body.rim().len(), darts);

        let defects = body
            .scaffold()
            .coordination_defects()
            .expect("the realization carries its links");
        for (vertex, defect) in &defects {
            match defect {
                crate::LocalCoordinationDefect::InteriorCycle { coordination, .. } => {
                    if let Some(site) = body.layout.site(*vertex) {
                        assert_eq!(
                            *coordination,
                            SCAFFOLD_LINK_FOLD * body.layout.coordination(site.vertex),
                            "{}",
                            site.name
                        );
                    }
                }
                other => panic!("{vertex:?} is {other:?}, not an interior cycle"),
            }
        }
    }

    #[test]
    fn narrowing_to_the_derivations_incidences_refuses_the_rim_by_name_and_leaks_nothing() {
        let body = DerivationCurvatureBody::found(&four_cycle()).expect("the layout realizes");
        let reading = body.reading().expect("the narrowed standing conducts");

        assert_eq!(reading.aperture.conducted.len(), body.layout.sites().len());
        for vertex in body.rim() {
            assert_eq!(
                reading.aperture.refused.get(vertex),
                Some(&ApertureRefusal::InteriorCycleWithoutHinges),
                "{vertex:?}"
            );
        }
        // The load-bearing consequence: no retained hinge touches a refused vertex, so the aperture
        // is hinge-closed and `read` conducts instead of refusing `AperturePorous`.
        assert!(reading.aperture.refused_hinges.is_empty());
        assert!(reading.aperture.porous_vertices().is_empty());
        assert_eq!(
            reading.aperture.conducted_hinges.len(),
            body.layout.incidences().len()
        );
    }

    #[test]
    fn the_deficit_at_unit_response_is_the_recruitment_coordination_and_the_charge_is_not_graded() {
        let body = DerivationCurvatureBody::found(&star()).expect("the layout realizes");
        let reading = body.reading().expect("conducts");
        let deficits = body.named_deficits(&reading);

        let centre = deficits
            .iter()
            .find(|named| named.name == "star")
            .expect("the star's centre");
        assert_eq!(centre.coordination, 3);
        assert_eq!(centre.deficit, integer(3));
        assert_eq!(centre.combinatorial_charge, 3);
        for leaf in deficits.iter().filter(|named| named.kind == SiteKind::Symbol) {
            assert_eq!(leaf.coordination, 1);
            assert_eq!(leaf.deficit, integer(5));
        }
        // Total = 6*4 - 2*3 = 18, and it is not zero, so the flow has something to move.
        assert_eq!(reading.total_deficit(), integer(18));
    }

    // ---------------------------------------------------------------------------------------------
    // The gauge: the orbit before the agreement
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn the_two_frames_read_every_coordination_differently_and_return_the_same_deficit() {
        let body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let agreement = body.frame_agreement().expect("both frames read");

        // The orbit first. If this population were empty the agreement below would be a tautology.
        let orbit = agreement.coordination_orbit();
        assert_eq!(
            orbit.len(),
            agreement.pairs.len(),
            "the frames must differ at every conducted site, not at some"
        );
        for pair in &orbit {
            assert_ne!(pair.scaffold_coordination, pair.derivation_coordination);
        }
        assert!(agreement.fold_holds());
        assert!(!agreement.refused_scaffold.is_empty());

        // Only now is agreement evidence.
        assert!(
            agreement.deficit_disagreements().is_empty(),
            "{:?}",
            agreement.deficit_disagreements()
        );
        assert!(agreement.acts_nontrivially_and_agrees());
    }

    #[test]
    fn the_derivations_own_frame_is_computed_without_the_standing() {
        // The falsifier for "frame D is frame S under another name". Frame D is the circuit at unit
        // response; frame S reads whatever the standing spends. Found the same layout at response
        // three and frame S goes flat while frame D does not move at all, so the two must disagree
        // at every conducted site. A `frame_agreement` that read the standing twice would report
        // agreement here and this test would fail.
        let body =
            DerivationCurvatureBody::found_at_response(&four_cycle(), integer(3)).expect("realizes");
        let agreement = body.frame_agreement().expect("both frames read");
        assert_eq!(
            agreement.deficit_disagreements().len(),
            agreement.pairs.len(),
            "frame D followed the standing's response, so it is not a second frame"
        );
        for pair in agreement.deficit_disagreements() {
            assert!(pair.surface_deficit.is_zero(), "{}", pair.name);
            assert_eq!(pair.derivation_deficit, integer(4), "{}", pair.name);
        }
    }

    // ---------------------------------------------------------------------------------------------
    // The flow, both declared halves
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn a_nonzero_deficit_moves_under_the_flow_and_the_total_is_negated() {
        let mut body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let before = body.reading().expect("conducts").deficits();
        assert!(before.values().any(|deficit| !deficit.is_zero()));

        let walked = body.flow(1).expect("the flow applies");
        let step = &walked[0];
        assert!(step.moved_something(), "{step:?}");
        // The exact totals, not only the predicate: four sites of coordination two at unit response
        // give `4 * (6 - 2) = 16`, and Consequence 2 negates it. A `total_is_negated` that always
        // returned true would survive the predicate and not these.
        assert_eq!(step.total_before, integer(16));
        assert_eq!(step.total_after, integer(-16));
        assert!(step.total_is_negated());
        assert!(step.whole, "{:?}", step.unlifted);
        for moved in &step.moved {
            assert_ne!(moved.before, moved.after);
            assert!(
                !moved.passages.is_empty(),
                "an anonymous deficit at {}",
                moved.name
            );
        }
        // Every revision is named by the incidence it sits on and the passages that founded it.
        for revision in &step.revised {
            assert!(!revision.passages.is_empty(), "{}", revision.name);
            assert_ne!(revision.spent_before, revision.spent_after);
        }
    }

    #[test]
    fn a_flat_layout_stays_exactly_fixed_and_the_write_back_changes_no_response() {
        // A four-cycle has coordination two everywhere, so response three makes every deficit
        // exactly zero. The value is solved, not tuned: `6 - 2r = 0`.
        let mut body = DerivationCurvatureBody::found_at_response(&four_cycle(), integer(3))
            .expect("realizes");
        let reading = body.reading().expect("conducts");
        assert!(reading.is_flat(), "{:?}", reading.deficits());
        assert_eq!(reading.fixed_point(), CurvatureFixedPoint::Flat);

        let pristine = body.consumed_responses().clone();
        let walked = body.flow(2).expect("the flow applies");
        for step in &walked {
            assert!(!step.moved_something(), "{:?}", step.moved);
            assert!(step.total_before.is_zero() && step.total_after.is_zero());
        }
        assert_eq!(body.consumed_responses(), &pristine);
        assert!(body.consumption_population().is_empty());
    }

    #[test]
    fn a_bipartite_layout_with_unequal_parts_sits_fixed_at_nonzero_deficit_forever() {
        // The falsifier of "the flow drives every deficit to zero". A star has parts of size three
        // and one; at response four the traced deviations alternate exactly and every revision is
        // zero, while no deficit is.
        let mut body =
            DerivationCurvatureBody::found_at_response(&star(), integer(4)).expect("realizes");
        let reading = body.reading().expect("conducts");
        let deficits = body.named_deficits(&reading);

        let centre = deficits
            .iter()
            .find(|named| named.name == "star")
            .expect("the centre");
        assert_eq!(centre.deficit, integer(-6));
        for leaf in deficits.iter().filter(|named| named.kind == SiteKind::Symbol) {
            assert_eq!(leaf.deficit, integer(2));
        }
        assert!(!reading.is_flat());

        // Fixed, and the scale is confirmed by a route that reads no response at all.
        let scale = body.forced_component_scale().expect("bipartite");
        assert_eq!(scale.len(), 1);
        assert_eq!(*scale.values().next().expect("one component"), integer(2));
        match body.fixed_point().expect("classified") {
            CurvatureFixedPoint::AlternatingTracedDeviation { component_scale } => {
                assert_eq!(component_scale, scale);
            }
            other => panic!("{other:?}"),
        }

        let walked = body.flow(3).expect("the flow applies");
        for step in &walked {
            assert!(!step.moved_something(), "step {} moved", step.ordinal);
            assert_eq!(step.total_before, step.total_after);
        }
        // Still nonflat after three steps: the deficits are fixed, not driven to zero.
        let after = body.reading().expect("conducts");
        assert!(!after.is_flat());
        assert_eq!(after.deficits(), reading.deficits());
    }

    // ---------------------------------------------------------------------------------------------
    // The partial arm
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn an_incidence_spending_nothing_along_its_own_edge_is_deposited_and_the_rest_are_lifted() {
        let mut body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let hinge = *body
            .layout
            .incidences()
            .keys()
            .next()
            .expect("a first incidence");
        let refused = body.refuse_one_lift(hinge).expect("the incidence exists");

        let walked = body.flow(1).expect("the flow applies");
        let step = &walked[0];
        assert!(!step.whole, "the partial arm must have deposited something");
        assert_eq!(step.unlifted.len(), 1, "{:?}", step.unlifted);
        let deposited = &step.unlifted[0];
        assert_eq!(deposited.hinge, hinge);
        assert_eq!(deposited.name, refused.name);
        assert!(!deposited.passages.is_empty());
        assert!(
            !deposited.refusal.requested.is_zero(),
            "the law asked this incidence for a nonzero scalar and no lift could reach it"
        );
        assert!(
            deposited
                .refusal
                .response_direction
                .dot(&deposited.refusal.edge_vector)
                .is_zero(),
            "the deposited refusal must carry the geometry that caused it"
        );
        // And what could be lifted was: the other three incidences were revised.
        assert_eq!(step.revised.len(), body.layout.incidences().len() - 1);
        // The refused incidence's response was left exactly as the layout carried it.
        assert_eq!(
            body.consumed_responses()[&hinge],
            body.pristine_responses()[&hinge]
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The write-back reaching the geometry
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn consuming_the_curvature_moves_the_geometry_local_stars_own_law_returns() {
        let mut body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let hinge = *body
            .layout
            .incidences()
            .keys()
            .next()
            .expect("a first incidence");

        // Before consuming anything the two enactments are the same standing, so the population
        // must be empty. Without this the test below cannot tell a wiring from a coincidence.
        let unmoved = body
            .consume_into_geometry(hinge, integer(1))
            .expect("the event enacts");
        assert!(
            !unmoved.moved_the_geometry(),
            "{:?}",
            unmoved.displaced
        );

        body.flow(1).expect("the flow applies");
        assert!(!body.consumption_population().is_empty());

        let consumed = body
            .consume_into_geometry(hinge, integer(1))
            .expect("the event enacts");
        assert!(
            consumed.moved_the_geometry(),
            "the write-back reached no position"
        );
        assert_ne!(consumed.response_before, consumed.response_after);
        for displaced in &consumed.displaced {
            assert_ne!(displaced.without_consumption, displaced.with_consumption);
            assert_eq!(
                displaced.difference,
                displaced
                    .with_consumption
                    .subtract(&displaced.without_consumption)
            );
        }
        // The displacement law at `local_star.rs:2082` moves exactly the driven hinge's two
        // endpoints, and the realized positions of the rest are read against them.
        let moved: BTreeSet<VertexId> = consumed
            .displaced
            .iter()
            .map(|displaced| displaced.vertex)
            .collect();
        let incidence = body.layout.incidence(hinge).expect("carried");
        assert!(
            incidence
                .endpoints
                .iter()
                .any(|endpoint| moved.contains(endpoint)),
            "neither endpoint of the driven incidence moved"
        );
    }

    #[test]
    fn a_zero_source_current_spends_no_response_however_the_curvature_was_revised() {
        // The negative pole: the write-back can only reach the geometry through a coordinate
        // change, so an event that drives nothing must return the empty population even after the
        // responses have been revised. A test that only ever saw motion could not tell the
        // consumption from the enactment.
        let mut body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let hinge = *body.layout.incidences().keys().next().expect("an incidence");
        body.flow(1).expect("the flow applies");
        let quiet = body
            .consume_into_geometry(hinge, integer(0))
            .expect("the event enacts");
        assert!(quiet.displaced.is_empty(), "{:?}", quiet.displaced);
        assert_ne!(quiet.response_before, quiet.response_after);
    }

    // ---------------------------------------------------------------------------------------------
    // The predicates, at both poles
    //
    // `discrete_curvature`'s Consequence 2 makes `total_is_negated` true of every step the carrier
    // can produce, and the fold law makes `fold_holds` true of every realization this module can
    // build. A predicate that cannot come out false on the material it reads carries no evidence —
    // `CLAUDE.md` §8's tautology rule — so each is exercised here on constructed values at both
    // poles, which is the only place its negative pole exists.
    // ---------------------------------------------------------------------------------------------

    fn step_with(before: Rat, after: Rat) -> NamedFlowStep {
        NamedFlowStep {
            ordinal: 1,
            moved: Vec::new(),
            still: Vec::new(),
            revised: Vec::new(),
            unlifted: Vec::new(),
            total_before: before,
            total_after: after,
            whole: true,
        }
    }

    #[test]
    fn the_negation_predicate_has_a_negative_pole() {
        assert!(step_with(integer(16), integer(-16)).total_is_negated());
        assert!(!step_with(integer(16), integer(16)).total_is_negated());
        assert!(!step_with(integer(16), integer(-15)).total_is_negated());
        // Zero is negated by itself, and that is the correct reading rather than an exception.
        assert!(step_with(integer(0), integer(0)).total_is_negated());
    }

    fn pair_with(scaffold: usize, derivation: usize, surface: Rat, derived: Rat) -> FramePair {
        FramePair {
            vertex: VertexId(1),
            name: "declared".to_owned(),
            scaffold_coordination: scaffold,
            derivation_coordination: derivation,
            surface_deficit: surface,
            derivation_deficit: derived,
        }
    }

    fn agreement_over(pairs: Vec<FramePair>) -> FrameAgreement {
        FrameAgreement {
            schema: "declared".to_owned(),
            pairs,
            refused_scaffold: Vec::new(),
        }
    }

    #[test]
    fn the_frame_predicates_have_negative_poles() {
        let acting = agreement_over(vec![pair_with(9, 3, integer(3), integer(3))]);
        assert!(acting.fold_holds());
        assert!(acting.acts_nontrivially_and_agrees());

        // A gauge whose two readings coincide has an empty orbit, and agreement under it is not
        // evidence however exactly the deficits match.
        let trivial = agreement_over(vec![pair_with(3, 3, integer(3), integer(3))]);
        assert!(trivial.coordination_orbit().is_empty());
        assert!(!trivial.acts_nontrivially_and_agrees());

        // The orbit acts and the deficits disagree: also refused.
        let split = agreement_over(vec![pair_with(9, 3, integer(3), integer(4))]);
        assert!(!split.deficit_disagreements().is_empty());
        assert!(!split.acts_nontrivially_and_agrees());

        // The fold law fails on a realization that is not the threefold thickening.
        let drifted = agreement_over(vec![pair_with(8, 3, integer(3), integer(3))]);
        assert!(!drifted.fold_holds());
    }

    // ---------------------------------------------------------------------------------------------
    // The reduction the bridge performs, exercised on this material
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn the_response_founded_on_an_incidence_is_oblique_to_its_own_edge() {
        // If responses were parallel to their edges, "keep the response's line" and "use the edge's
        // line" would be the same line and the lift could substitute the edge without any test
        // noticing. Every founded response here has a nonzero component the projection cannot see.
        let body = DerivationCurvatureBody::found(&four_cycle()).expect("realizes");
        let reading = body.reading().expect("conducts");
        for projection in reading.projections.values() {
            assert_eq!(projection.along_edge, integer(UNIT_RESPONSE));
            assert!(
                !projection
                    .response_direction
                    .cross(&projection.edge_vector)
                    .norm_squared()
                    .is_zero(),
                "hinge {:?} carries a response parallel to its own edge",
                projection.hinge
            );
        }
    }
}
