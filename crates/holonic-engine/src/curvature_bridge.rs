//! The layout-to-curvature bridge: what a hinge spends along its own edge.
//!
//! # What this wires
//!
//! `local_star` computes a discrete disclination charge at every vertex
//! (`local_star.rs:1143`, published by `LocalStarStanding::coordination_defects`)
//! and then discards it: the successor standing clones `geometry_responses`
//! verbatim at `local_star.rs:2301`, so the response population that produced
//! the curvature is a constant of the motion.
//!
//! `discrete_curvature` owns the law that would revise it, on a bare hinge
//! incidence carrying one exact rational per hinge. This module is the only
//! thing between them, and it is not free: `local_star` carries a
//! `BTreeMap<HingeId, RatVec3>` and the curvature law wants a
//! `BTreeMap<HingeId, Rat>`. Three conversions are named below, one of which
//! is genuinely lossy in the direction that matters.
//!
//! The loop is closed by a driver:
//! `crates/holonic-engine/examples/layout_curvature_consumption.rs`. It builds
//! standings, enters at the response population, iterates [`revise`] and
//! [`revise_partially`], and returns the revision, deficit, leak and
//! unlifted-hinge **populations** — not their sizes. Its assertions are the
//! falsifiers `blueprint/THE_ASSEMBLY.md` names for loop (b), so a wrong bridge
//! makes the driver exit nonzero.
//!
//! Nothing here is approximate. Every quantity is an exact `Rat` or an exact
//! `RatVec3` over `BigRational`. There is no float, no tolerance, no
//! threshold, no rate, no weight, and nothing ordered by magnitude.
//!
//! # The reduction: DOT, never `norm_squared`
//!
//! At `local_star.rs:2082` the layout spends a response as
//!
//! ```text
//! displacement = geometry_responses[hinge] * (coordinate_change / 2)
//! lower -= displacement            upper += displacement
//! ```
//!
//! so the response is spent as a *separation of that hinge's own two
//! endpoints*. The part of it that changes the hinge's edge is therefore its
//! component along that edge, and the scalar the curvature law must receive is
//!
//! ```text
//! along_edge(e) = geometry_responses[e] . edge_vector(e)
//! ```
//!
//! where `edge_vector(e)` is `LocalSpatialStanding::edges[e].vector`, i.e.
//! `position(upper) - position(lower)` — read from the translation-free
//! spatial carrier directly rather than by realizing absolute positions, so no
//! component root enters the reduction.
//!
//! **`norm_squared` is refused.** It is direction-blind: a response pointing
//! along its edge and a response pointing against it have the same
//! `norm_squared`, so a bridge built on it cannot tell an expanding hinge from
//! a contracting one, and every deficit it returned would be a magnitude with
//! its sign thrown away. [`HingeResponseProjection`] retains
//! `direction_blind_norm_squared` next to `along_edge` for exactly one reason:
//! so that a reader can see what the refused reduction would have said, and so
//! that a test can exhibit two hinges on which the two disagree. It is the
//! **response's** norm-squared, never the edge's, and
//! `the_projection_carries_the_whole_record_and_not_only_the_scalar` pins that
//! on a fixture where the two differ.
//!
//! The reduction is still a reduction. The mitigation is that the projection
//! is **deposited whole** — the `RatVec3` response, the `RatVec3` edge vector
//! and the scalar are carried together in one record, so the next organ
//! receives the population and not just the number.
//!
//! # Every refusal is a population
//!
//! `blueprint/THE_ASSEMBLY.md:151`: *no adapter may reduce one of these
//! structures to a boolean or a scalar on its way to the next organ; gate on
//! the boolean if you must, deposit the population.* That rule binds the
//! refusals as hard as it binds the returns, and two of them broke it until
//! 2026-08-08:
//!
//! - [`read`] now establishes porosity itself, from
//!   [`CurvatureAperture::porous_vertices`], and refuses with the **whole leak
//!   population** rather than the one vertex the carrier happened to name
//!   first. This also fixes a misreport: a conducted vertex *all* of whose
//!   hinges are refused made `found` return `IsolatedVertex` before its
//!   incidence comparison, so total porosity used to surface as `Carrier(..)`.
//! - [`step`] collects **every** hinge whose lift is undefined and refuses with
//!   that population, rather than returning the first one and dropping the
//!   rest.
//!
//! `DiscreteCurvatureConfiguration::found` still certifies the same fact
//! independently, and that second frame is exercised rather than assumed:
//! `the_carriers_own_incidence_certification_is_a_second_frame_on_the_leak_population`
//! hands `found` the porous aperture directly and requires the vertex it names
//! to be a member of the leak population the bridge computed.
//!
//! # The declared aperture, and where the link size comes from
//!
//! The aperture is the **interior-cycle vertex subpopulation**: the vertices
//! at which `local_star` itself returns
//! `LocalCoordinationDefect::InteriorCycle`. A boundary path, a singular link
//! and an isolated vertex have no `6 - |link|` doctrine at
//! `local_star.rs:1151` and none is invented here; they are returned as typed
//! refusals in [`CurvatureAperture::refused`], as a population, and that is
//! correct behaviour rather than a gap.
//!
//! The link size handed to `DiscreteCurvatureConfiguration::found` is
//! **counted from hinge incidence** — the number of hinges of the complex
//! whose edge touches the vertex — and not from
//! `VertexStarLink::link_vertices.len()`.
//!
//! # Two frames, and the material on which they disagree
//!
//! [`ApertureVertex`] carries both readings of one vertex's coordination:
//! `link_coordination`/`link_charge` from `local_star`'s face-derived link, and
//! `incident_hinges`/`hinge_charge` from the complex's hinge incidence.
//!
//! **On a standing exactly as `LocalStarLaw::initial_standing` returned it the
//! two cannot disagree, and that is a theorem, not a coincidence:**
//!
//! - every hinge has exactly two cofaces (`found_hinge`, `simplicial.rs:265`),
//!   so a hinge at `v` is a face edge `{v, x}` with `x` in `v`'s link, and
//!   hinge edges are unique, so `#hinges(v) <= |link_vertices(v)|`;
//! - `LocalStarLaw::face_fields` refuses a standing in which any face boundary
//!   edge lacks a hinge (`LocalStarError::MissingBoundaryHinge`), so every
//!   `{v, x}` with `x` in the link carries a hinge, giving `>=`.
//!
//! **A founding standing is not the only standing.** `HingeWorldStanding`
//! documents its own complex as *"contemporary oriented incidence. The law
//! supplies the founding complex, but later topology deeds replace this
//! standing value atomically"* (`simplicial.rs:826-828`). A standing whose
//! hinge population is narrower than its face-edge population — a retired
//! hinge, a subcomplex reading — is exactly what that sentence describes, it is
//! a value of the public carrier, and on it the two frames **do** disagree.
//! `a_narrowed_hinge_population_makes_the_two_coordination_frames_disagree`
//! exhibits an octahedron whose four equatorial hinges have been retired: each
//! equatorial vertex reads coordination `4` in the face frame and `2` in the
//! hinge frame, so `link_charge` is `2` while `hinge_charge` is `4`.
//! [`ApertureVertex::frames_agree`] is therefore a check with material on both
//! sides, and [`CurvatureBridgeReading::frame_disagreements`] returns that
//! population rather than a flag.
//!
//! The same narrowing makes two further things reachable, and both were
//! previously written here as impossible:
//!
//! - **[`ApertureRefusal::InteriorCycleWithoutHinges`]** fires on a vertex
//!   whose every hinge has been retired.
//! - **The carrier's nonflat fixed points are reachable through this bridge.**
//!   The retired-equator octahedron *is* `K(2,4)`: uniform response `9/4`
//!   leaves the four equatorial deficits at `3/2`, the two apex deficits at
//!   `-3`, every hinge revision exactly zero, and
//!   `forced_component_scale` at `3/4`. What is true — and is all that was
//!   ever proved — is that a **hinge-closed** interior-cycle aperture always
//!   contains a whole triangle (`v`, `x_i`, `x_{i+1}` for consecutive link
//!   vertices, all three edges being face edges and therefore hinges), so it
//!   always carries an odd hinge cycle and by `discrete_curvature`'s
//!   Consequence 3 can only be fixed when flat.
//!
//! Removing a **face** from a standing's complex — the same documented
//! lifecycle — reaches [`ApertureRefusal::BoundaryPath`], which was recorded
//! here as a dead arm until 2026-08-08.
//!
//! ## Every declared refusal, and what exercises it
//!
//! | refusal | reachable | exercised by |
//! |---|---|---|
//! | [`ApertureRefusal::BoundaryPath`] | on a narrowed face population | `a_withheld_face_leaves_a_boundary_path_the_aperture_refuses_by_name` |
//! | [`ApertureRefusal::SingularLink`] | yes | `a_singular_link_an_isolated_vertex_and_a_porous_interior_are_typed_refusals` |
//! | [`ApertureRefusal::IsolatedLink`] | yes | the same |
//! | [`ApertureRefusal::InteriorCycleWithoutHinges`] | on a narrowed hinge population | `an_interior_cycle_carrying_no_hinge_is_refused_by_name` |
//! | [`CurvatureBridgeError::EmptyAperture`] | on a narrowed hinge population | `a_standing_carrying_no_conducted_vertex_refuses_the_whole_aperture` |
//! | [`CurvatureBridgeError::AperturePorous`] | yes | `a_singular_link_…`, `a_conducted_vertex_whose_every_hinge_is_refused_reports_porosity` |
//! | [`CurvatureBridgeError::MissingGeometryResponse`] | yes | `a_missing_response_and_a_missing_edge_vector_are_typed_refusals` |
//! | [`CurvatureBridgeError::MissingSpatialEdge`] | yes | the same |
//! | [`CurvatureBridgeError::ResponsesOrthogonalToTheirOwnEdges`] | yes | `the_lift_refuses_every_response_that_spends_nothing_along_its_own_edge` |
//! | [`CurvatureBridgeError::Coordination`] | **no** | — |
//! | [`CurvatureBridgeError::Carrier`] | **no** from [`read`] | — |
//!
//! The last two are stated as unreachable rather than claimed as exercised.
//! `Coordination` propagates `LocalStarStanding::coordination_defects`, which
//! maps over the complex's own vertex keys while `vertex_star_link` refuses
//! only an absent pivot; no input can make it fire, and it exists because the
//! upstream signature is fallible and the compiler requires the arm. `Carrier`
//! propagates `DiscreteCurvatureConfiguration::found`, whose every refusal is
//! excluded upstream by this module: duplicate ids cannot arise from a
//! `BTreeMap`, endpoints are conducted by construction, self-incidence is
//! refused by `Edge::new`, and both `IsolatedVertex` and
//! `DeclaredLinkSizeDisagreesWithIncidence` are established and refused by the
//! porosity pre-check. Neither is counted as evidence anywhere.
//!
//! # The write-back, which is not a function
//!
//! The flow returns one exact increment per hinge and the standing wants a
//! `RatVec3`. There is no map `Rat -> RatVec3`. Over a fixed edge direction
//! `d`, the fibre above a requested scalar `s` is the affine plane
//! `{ w : w . d = s }`, which is two-dimensional; choosing a point in it
//! requires information the layout never supplied.
//!
//! The one lift that adds nothing is the one that never leaves the line the
//! layout already carried:
//!
//! ```text
//! after = before * (along_edge_after / along_edge_before)
//! ```
//!
//! It keeps the response's line verbatim — `after` is an exact rational
//! multiple of `before`, so `after x before = 0` — and revises only the
//! magnitude, together with the sense along that line when the factor is
//! negative. It satisfies `after . d = along_edge_after` exactly.
//!
//! It is defined **exactly when `along_edge_before` is nonzero**, and where
//! that fails [`lift_along_edge`] REFUSES with an [`OrthogonalHinge`] — the
//! whole geometry of the hinge that could not be lifted, which for a one-hinge
//! organ *is* its refusal population. The fibre is not empty there — it is that
//! it contains no point on the line through `before`, so every candidate
//! differs from `before` along a direction the layout never spent. **Picking a
//! canonical direction there (an axis, the edge itself, the component mean)
//! would invent geometry the layout did not have, and the invented component
//! would then be spent at `local_star.rs:2082` as though it had been
//! constitutive data.** That is the same defect as an absolute frame folded
//! into a lineage, and it is refused rather than defaulted.
//!
//! A zero *successor* scalar is a different matter and is admitted: the factor
//! is exactly zero, the response collapses to the zero vector, and the next
//! reading of that hinge projects to zero and is refused by the rule above.
//! That terminus is reached by the law, not chosen by the bridge.
//!
//! # What the flow does and does not do
//!
//! `discrete_curvature`'s update law negates the total deficit at every step
//! and preserves its magnitude exactly. **It is not a smoothing and it does
//! not drive deficits to zero**, and a bridge run that claims convergence has
//! mis-graded. On any aperture reachable from a whole-hinge `LocalStarStanding`
//! the total deficit is an exact involution: `12` and `-12` forever on a
//! triangulated sphere, never zero. On a narrowed one the nonflat fixed point
//! is reachable and is fixed at nonzero deficit forever, which is the same
//! statement from the other side.
//!
//! Grade the **deficit**, not the combinatorial charge. The charge is
//! `6 - n_v` and moves only when the complex changes, so a run that grades it
//! sees a flow step move nothing and concludes wrongly.
//!
//! # Three arms at `local_star.rs:2301`, not two
//!
//! Measured 2026-08-07. Consuming [`step`] at the successor's
//! `geometry_responses.clone()` was tried two ways against the local-star
//! suite:
//!
//! - **Propagating the refusal: 14 of 21 local-star tests fail.** All fourteen
//!   fail on one refusal — `local_star`'s own octahedral fixture assigns
//!   hinge 10 the response `(1,0,0)` while its edge `c-f` carries the vector
//!   `(0,-3,-4)`, so that response spends exactly nothing along its own edge
//!   and no honest lift exists for it.
//! - **Falling open on the refusal: all 21 pass — because the wiring does
//!   nothing.** The first refusal discarded the whole revised population and
//!   restored the clone, so a green suite there measured a no-op wearing a
//!   wiring's name.
//!
//! **That was a false dichotomy and the design already prescribed the third
//! arm** (`blueprint/THE_ASSEMBLY.md:151`): apply the lift where it is defined,
//! gate on the boolean, deposit the refused hinges as a population. It is built
//! — [`step_partially`] and [`revise_partially`] — and it is measured, in
//! `the_partial_arm_lifts_what_it_can_and_deposits_what_it_cannot`, on an
//! octahedron reproducing the local-star fixture's defect: ten of twelve hinges
//! are revised, two are deposited whole, the deficit moves, and the discrepancy
//! against the carrier's own successor is exactly the retained increment at the
//! four endpoints of the two unlifted hinges and exactly zero everywhere else.
//! That is a falsifiable statement about the arm rather than a green suite.
//!
//! Whether the event law *should* take that arm is not decided here and cannot
//! be decided from this file: `local_star.rs:2301` is another module's owner.
//! What is decided is that [`revise`] and [`revise_partially`] are callers'
//! deeds, so a standing receives its own curvature when something asks it to,
//! and the driver named at the top of this file is the something.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::{Rat, RatVec3};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::discrete_curvature::{
    CurvatureFixedPoint, CurvatureFlowStep, DiscreteCurvatureConfiguration, DiscreteCurvatureError,
    FLAT_COORDINATION,
};
use crate::{Edge, HingeId, LocalCoordinationDefect, LocalStarError, LocalStarStanding, VertexId};

/// One conducted hinge whose response spends exactly nothing along its own
/// edge, carried whole so the refusal is legible without a second lookup.
///
/// This is the complete refusal of [`lift_along_edge`]. A one-hinge organ's
/// refusal population has one member by construction; [`step`] collects these
/// across the aperture and refuses with the population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrthogonalHinge {
    pub hinge: HingeId,
    pub edge: Edge,
    /// The response the layout carries, which the lift may not leave.
    pub response_direction: RatVec3,
    /// The edge it spends nothing along.
    pub edge_vector: RatVec3,
    /// The scalar the lift was asked to reach and cannot.
    pub requested: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum CurvatureBridgeError {
    #[error("the standing could not return its coordination defects: {0}")]
    Coordination(#[from] LocalStarError),
    #[error("hinge {hinge:?} carries no direction in the standing's `geometry_responses`")]
    MissingGeometryResponse { hinge: HingeId },
    #[error("the spatial standing carries no vector for edge {edge:?} of hinge {hinge:?}")]
    MissingSpatialEdge { hinge: HingeId, edge: Edge },
    #[error(
        "the standing carries no interior-cycle vertex with an incident hinge, so the declared \
         aperture is empty"
    )]
    EmptyAperture,
    #[error(
        "the interior-cycle aperture is not closed under hinge incidence, so these vertices would \
         under-count their deficits; the whole leaking population is carried: {leaks:?}"
    )]
    AperturePorous {
        leaks: BTreeMap<VertexId, ApertureLeak>,
    },
    #[error("the curvature carrier refused the declared aperture: {0}")]
    Carrier(#[from] DiscreteCurvatureError),
    #[error(
        "these hinges spend exactly nothing along their own edges, so no revision of their \
         magnitudes reaches the requested scalars; a lift that supplied the missing direction \
         would invent geometry the layout never carried: {refused:?}"
    )]
    ResponsesOrthogonalToTheirOwnEdges {
        refused: BTreeMap<HingeId, OrthogonalHinge>,
    },
}

/// Why a vertex of the complex sits outside the declared aperture.
///
/// Each of these is a typed structural fact `local_star` already returns. None
/// of them is a failure and none is repaired here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ApertureRefusal {
    /// `LocalCoordinationDefect::BoundaryPath`. The `6 - |link|` charge is
    /// declared only for a cycle link at `local_star.rs:1151`.
    BoundaryPath { coordination: usize },
    /// `LocalCoordinationDefect::Singular`.
    SingularLink { coordination: usize },
    /// `LocalCoordinationDefect::Isolated`.
    IsolatedLink,
    /// An interior cycle carrying no hinge at all. `n_v = 0` makes the traced
    /// deviation `K(v)/n_v` undefined, which `discrete_curvature` refuses as
    /// `IsolatedVertex`; it is named here so the reason survives.
    InteriorCycleWithoutHinges,
}

/// One conducted vertex, with its coordination read in both available frames.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApertureVertex {
    pub vertex: VertexId,
    /// `local_star`'s own link cardinality, verbatim from
    /// `LocalCoordinationDefect::InteriorCycle::coordination`. Face-derived.
    pub link_coordination: usize,
    /// `local_star`'s own charge, verbatim from
    /// `LocalCoordinationDefect::InteriorCycle::charge`. Face-derived.
    pub link_charge: i64,
    /// `n_v` counted from hinge incidence over the whole complex. This is what
    /// the curvature carrier is told.
    pub incident_hinges: usize,
    /// `FLAT_COORDINATION - n_v`, the charge the carrier will return.
    pub hinge_charge: i64,
}

impl ApertureVertex {
    /// Whether the face-derived and hinge-derived charges coincide.
    ///
    /// Both outcomes have material: identical on a standing whose hinge
    /// population is its face-edge population, different once a hinge has been
    /// retired. See the module documentation.
    pub fn frames_agree(&self) -> bool {
        self.link_charge == self.hinge_charge
    }
}

/// One hinge the aperture does not conduct, with the endpoint that put it out.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefusedHinge {
    pub hinge: HingeId,
    pub edge: Edge,
    /// An endpoint lying outside the aperture; the lower one when both do.
    pub exterior: VertexId,
}

/// A conducted vertex whose hinges do not all lie inside the aperture. Its
/// deficit would under-count, so the reading refuses rather than reporting it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApertureLeak {
    pub vertex: VertexId,
    pub incident_in_complex: usize,
    pub incident_in_aperture: usize,
}

/// The declared aperture, with every refusal returned as a population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurvatureAperture {
    pub schema: String,
    /// Interior-cycle vertices carrying at least one hinge.
    pub conducted: BTreeMap<VertexId, ApertureVertex>,
    /// Every other vertex of the complex, with its typed reason.
    pub refused: BTreeMap<VertexId, ApertureRefusal>,
    /// Hinges both of whose endpoints are conducted.
    pub conducted_hinges: BTreeSet<HingeId>,
    /// Hinges refused because at least one endpoint is outside the aperture.
    pub refused_hinges: BTreeMap<HingeId, RefusedHinge>,
}

impl CurvatureAperture {
    /// Conducted vertices at which the aperture drops a hinge the complex
    /// carries. Nonempty exactly when [`read`] refuses with
    /// [`CurvatureBridgeError::AperturePorous`], which carries this whole map.
    pub fn porous_vertices(&self) -> BTreeMap<VertexId, ApertureLeak> {
        let mut lost: BTreeMap<VertexId, usize> = BTreeMap::new();
        for refused in self.refused_hinges.values() {
            for endpoint in [refused.edge.lower, refused.edge.upper] {
                if self.conducted.contains_key(&endpoint) {
                    *lost.entry(endpoint).or_insert(0) += 1;
                }
            }
        }
        lost.into_iter()
            .map(|(vertex, dropped)| {
                let incident_in_complex = self.conducted[&vertex].incident_hinges;
                (
                    vertex,
                    ApertureLeak {
                        vertex,
                        incident_in_complex,
                        incident_in_aperture: incident_in_complex - dropped,
                    },
                )
            })
            .collect()
    }
}

/// One hinge's response, its own edge, and the exact scalar the layout spends
/// along that edge. The whole record travels; the scalar never travels alone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeResponseProjection {
    pub hinge: HingeId,
    pub edge: Edge,
    /// Verbatim from `LocalStarStanding::geometry_responses`.
    pub response_direction: RatVec3,
    /// Verbatim from `LocalSpatialStanding::edges[edge].vector`, which is
    /// `position(upper) - position(lower)`.
    pub edge_vector: RatVec3,
    /// `response_direction . edge_vector`. Signed: positive expands the hinge,
    /// negative contracts it.
    pub along_edge: Rat,
    /// `response_direction . response_direction` — the RESPONSE's, never the
    /// edge's — retained only so a reader can see what the refused
    /// direction-blind reduction would have said. Nothing in this module or
    /// downstream consumes it.
    pub direction_blind_norm_squared: Rat,
}

/// One honest lift of a revised scalar back into the layout's carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeometryResponseRevision {
    pub hinge: HingeId,
    pub edge: Edge,
    pub before: RatVec3,
    pub after: RatVec3,
    pub along_edge_before: Rat,
    pub along_edge_after: Rat,
    /// `along_edge_after / along_edge_before`. The lift is
    /// `after = before.scale(&magnitude_factor)`, so the line is carried
    /// verbatim and only the magnitude, and at a negative factor the sense
    /// along that line, is revised.
    pub magnitude_factor: Rat,
}

/// One complete reading of a standing through the curvature carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurvatureBridgeReading {
    pub schema: String,
    pub aperture: CurvatureAperture,
    pub projections: BTreeMap<HingeId, HingeResponseProjection>,
    pub configuration: DiscreteCurvatureConfiguration,
}

impl CurvatureBridgeReading {
    pub fn deficits(&self) -> BTreeMap<VertexId, Rat> {
        self.configuration.deficits()
    }

    pub fn total_deficit(&self) -> Rat {
        self.configuration.total_deficit()
    }

    /// The purely combinatorial charge per conducted vertex, in the **hinge**
    /// frame. It moves only when the complex changes; grading a flow step by it
    /// reports nothing.
    pub fn combinatorial_charges(&self) -> BTreeMap<VertexId, i64> {
        self.aperture
            .conducted
            .iter()
            .map(|(vertex, carried)| (*vertex, carried.hinge_charge))
            .collect()
    }

    pub fn fixed_point(&self) -> CurvatureFixedPoint {
        self.configuration.fixed_point()
    }

    pub fn is_flat(&self) -> bool {
        self.configuration.is_flat()
    }

    /// Conducted vertices whose face-derived and hinge-derived charges differ.
    /// The population, never a flag.
    pub fn frame_disagreements(&self) -> BTreeMap<VertexId, ApertureVertex> {
        self.aperture
            .conducted
            .iter()
            .filter(|(_, carried)| !carried.frames_agree())
            .map(|(vertex, carried)| (*vertex, *carried))
            .collect()
    }
}

/// One application of the curvature law in which **every** conducted hinge was
/// lifted. [`step`] returns this or refuses; the emptiness of the unlifted
/// population is carried by the type rather than by a field that cannot vary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurvatureBridgeStep {
    pub schema: String,
    pub before: CurvatureBridgeReading,
    /// The carrier's own complete record of the step, deficits included.
    pub flow: CurvatureFlowStep,
    pub revisions: BTreeMap<HingeId, GeometryResponseRevision>,
    /// The successor response population: every conducted hinge revised, every
    /// hinge outside the aperture carried verbatim. This is the value that
    /// `local_star.rs:2301` clones today.
    pub revised_geometry_responses: BTreeMap<HingeId, RatVec3>,
}

/// One application of the curvature law that lifted what it could and
/// **deposited what it could not**, per `blueprint/THE_ASSEMBLY.md:151`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PartialCurvatureBridgeStep {
    pub schema: String,
    pub before: CurvatureBridgeReading,
    pub flow: CurvatureFlowStep,
    pub revisions: BTreeMap<HingeId, GeometryResponseRevision>,
    /// Every conducted hinge the lift refused, carried whole. The population,
    /// never a count and never a flag.
    pub unlifted: BTreeMap<HingeId, OrthogonalHinge>,
    /// The successor response population: every lifted hinge revised, every
    /// unlifted and every non-conducted hinge carried verbatim.
    pub revised_geometry_responses: BTreeMap<HingeId, RatVec3>,
}

impl PartialCurvatureBridgeStep {
    /// Whether every conducted hinge was lifted. This is the boolean the design
    /// permits a caller to gate on; the population is [`Self::unlifted`].
    pub fn is_whole(&self) -> bool {
        self.unlifted.is_empty()
    }

    /// Promote to a whole step, or return the population that refused.
    pub fn into_whole(self) -> Result<CurvatureBridgeStep, BTreeMap<HingeId, OrthogonalHinge>> {
        if !self.unlifted.is_empty() {
            return Err(self.unlifted);
        }
        Ok(CurvatureBridgeStep {
            schema: "holonic-engine.curvature-bridge-step.v1".to_owned(),
            before: self.before,
            flow: self.flow,
            revisions: self.revisions,
            revised_geometry_responses: self.revised_geometry_responses,
        })
    }
}

/// Declare the aperture: which vertices conduct, which refuse and why, and
/// which hinges lie wholly inside.
pub fn declare_aperture(
    standing: &LocalStarStanding,
) -> Result<CurvatureAperture, CurvatureBridgeError> {
    let complex = &standing.kinematic.complex;

    // Link sizes are counted FROM HINGE INCIDENCE, never from
    // `VertexStarLink::link_vertices.len()`.
    let mut incident: BTreeMap<VertexId, BTreeSet<HingeId>> = complex
        .vertices
        .keys()
        .map(|vertex| (*vertex, BTreeSet::new()))
        .collect();
    for hinge in complex.hinges.values() {
        incident.entry(hinge.edge.lower).or_default().insert(hinge.id);
        incident.entry(hinge.edge.upper).or_default().insert(hinge.id);
    }

    let mut conducted = BTreeMap::new();
    let mut refused = BTreeMap::new();
    for (vertex, defect) in standing.coordination_defects()? {
        let hinges = incident.get(&vertex).map_or(0, BTreeSet::len);
        match defect {
            LocalCoordinationDefect::InteriorCycle {
                coordination,
                charge,
            } => {
                if hinges == 0 {
                    refused.insert(vertex, ApertureRefusal::InteriorCycleWithoutHinges);
                } else {
                    conducted.insert(
                        vertex,
                        ApertureVertex {
                            vertex,
                            link_coordination: coordination,
                            link_charge: charge,
                            incident_hinges: hinges,
                            hinge_charge: FLAT_COORDINATION
                                - i64::try_from(hinges)
                                    .expect("a finite local hinge incidence fits i64"),
                        },
                    );
                }
            }
            LocalCoordinationDefect::BoundaryPath { coordination } => {
                refused.insert(vertex, ApertureRefusal::BoundaryPath { coordination });
            }
            LocalCoordinationDefect::Singular { coordination } => {
                refused.insert(vertex, ApertureRefusal::SingularLink { coordination });
            }
            LocalCoordinationDefect::Isolated => {
                refused.insert(vertex, ApertureRefusal::IsolatedLink);
            }
        }
    }
    if conducted.is_empty() {
        return Err(CurvatureBridgeError::EmptyAperture);
    }

    let mut conducted_hinges = BTreeSet::new();
    let mut refused_hinges = BTreeMap::new();
    for hinge in complex.hinges.values() {
        let lower = conducted.contains_key(&hinge.edge.lower);
        let upper = conducted.contains_key(&hinge.edge.upper);
        if lower && upper {
            conducted_hinges.insert(hinge.id);
        } else {
            refused_hinges.insert(
                hinge.id,
                RefusedHinge {
                    hinge: hinge.id,
                    edge: hinge.edge,
                    exterior: if lower {
                        hinge.edge.upper
                    } else {
                        hinge.edge.lower
                    },
                },
            );
        }
    }

    Ok(CurvatureAperture {
        schema: "holonic-engine.curvature-bridge-aperture.v1".to_owned(),
        conducted,
        refused,
        conducted_hinges,
        refused_hinges,
    })
}

/// Project every conducted hinge's response onto its own edge.
pub fn project_responses(
    standing: &LocalStarStanding,
    aperture: &CurvatureAperture,
) -> Result<BTreeMap<HingeId, HingeResponseProjection>, CurvatureBridgeError> {
    let complex = &standing.kinematic.complex;
    let mut projections = BTreeMap::new();
    for id in &aperture.conducted_hinges {
        let hinge = complex
            .hinges
            .get(id)
            .expect("the aperture was declared from this complex's hinge population");
        let response_direction = standing
            .geometry_responses
            .get(id)
            .ok_or(CurvatureBridgeError::MissingGeometryResponse { hinge: *id })?
            .clone();
        let edge_vector = standing
            .spatial
            .edges
            .get(&hinge.edge)
            .ok_or(CurvatureBridgeError::MissingSpatialEdge {
                hinge: *id,
                edge: hinge.edge,
            })?
            .vector
            .clone();
        let along_edge = response_direction.dot(&edge_vector);
        let direction_blind_norm_squared = response_direction.norm_squared();
        projections.insert(
            *id,
            HingeResponseProjection {
                hinge: *id,
                edge: hinge.edge,
                response_direction,
                edge_vector,
                along_edge,
                direction_blind_norm_squared,
            },
        );
    }
    Ok(projections)
}

/// Read a standing's layout as a curvature configuration.
///
/// Porosity is established here, from [`CurvatureAperture::porous_vertices`],
/// and refused with the whole leak population. `found`'s own incidence
/// certification is retained as an independent second frame on the same fact.
pub fn read(standing: &LocalStarStanding) -> Result<CurvatureBridgeReading, CurvatureBridgeError> {
    let aperture = declare_aperture(standing)?;
    let leaks = aperture.porous_vertices();
    if !leaks.is_empty() {
        return Err(CurvatureBridgeError::AperturePorous { leaks });
    }
    let projections = project_responses(standing, &aperture)?;
    let complex = &standing.kinematic.complex;
    let configuration = DiscreteCurvatureConfiguration::found(
        aperture
            .conducted
            .values()
            .map(|carried| (carried.vertex, carried.incident_hinges)),
        projections.values().map(|projection| {
            let edge = complex.hinges[&projection.hinge].edge;
            (
                projection.hinge,
                [edge.lower, edge.upper],
                projection.along_edge.clone(),
            )
        }),
    )?;
    Ok(CurvatureBridgeReading {
        schema: "holonic-engine.curvature-bridge-reading.v1".to_owned(),
        aperture,
        projections,
        configuration,
    })
}

/// Lift one revised scalar back onto the line the layout already carried.
///
/// Refuses when the response spends exactly nothing along its own edge, with
/// the whole hinge geometry. This organ has exactly one refusal, so its error
/// type is that refusal rather than the module's enum. See the module
/// documentation for why no canonical direction is substituted.
pub fn lift_along_edge(
    projection: &HingeResponseProjection,
    along_edge_after: Rat,
) -> Result<GeometryResponseRevision, OrthogonalHinge> {
    if projection.along_edge.is_zero() {
        return Err(OrthogonalHinge {
            hinge: projection.hinge,
            edge: projection.edge,
            response_direction: projection.response_direction.clone(),
            edge_vector: projection.edge_vector.clone(),
            requested: along_edge_after,
        });
    }
    let magnitude_factor = &along_edge_after / &projection.along_edge;
    let after = projection.response_direction.scale(&magnitude_factor);
    Ok(GeometryResponseRevision {
        hinge: projection.hinge,
        edge: projection.edge,
        before: projection.response_direction.clone(),
        after,
        along_edge_before: projection.along_edge.clone(),
        along_edge_after,
        magnitude_factor,
    })
}

/// Apply the curvature law once, lifting every conducted hinge whose lift is
/// defined and depositing every hinge whose lift is not.
///
/// This is the design's own reviewable rule at
/// `blueprint/THE_ASSEMBLY.md:151`: gate on the boolean, deposit the
/// population. The standing is not mutated.
pub fn step_partially(
    standing: &LocalStarStanding,
) -> Result<PartialCurvatureBridgeStep, CurvatureBridgeError> {
    let before = read(standing)?;
    let mut configuration = before.configuration.clone();
    let flow = configuration.step();
    let mut revisions = BTreeMap::new();
    let mut unlifted = BTreeMap::new();
    let mut revised_geometry_responses = standing.geometry_responses.clone();
    for (hinge, projection) in &before.projections {
        let increment = flow
            .revisions
            .get(hinge)
            .expect("the carrier revises exactly the hinges the aperture supplied");
        let along_edge_after = &projection.along_edge + increment;
        match lift_along_edge(projection, along_edge_after) {
            Ok(revision) => {
                revised_geometry_responses.insert(*hinge, revision.after.clone());
                revisions.insert(*hinge, revision);
            }
            Err(refused) => {
                unlifted.insert(*hinge, refused);
            }
        }
    }
    Ok(PartialCurvatureBridgeStep {
        schema: "holonic-engine.curvature-bridge-partial-step.v1".to_owned(),
        before,
        flow,
        revisions,
        unlifted,
        revised_geometry_responses,
    })
}

/// Apply the curvature law once and lift EVERY revision back into a complete
/// successor `geometry_responses` population, or refuse with the whole
/// population of hinges that could not be lifted. The standing is not mutated.
pub fn step(standing: &LocalStarStanding) -> Result<CurvatureBridgeStep, CurvatureBridgeError> {
    step_partially(standing)?
        .into_whole()
        .map_err(|refused| CurvatureBridgeError::ResponsesOrthogonalToTheirOwnEdges { refused })
}

/// Apply one whole step and write the lifted responses into the standing.
///
/// This is the consumption `local_star.rs:2301` does not perform. It is a
/// caller's deed rather than an event-law side effect, so a standing only
/// receives its own curvature when something asks it to.
pub fn revise(standing: &mut LocalStarStanding) -> Result<CurvatureBridgeStep, CurvatureBridgeError> {
    let applied = step(standing)?;
    standing.geometry_responses = applied.revised_geometry_responses.clone();
    Ok(applied)
}

/// Apply one partial step and write the lifted responses into the standing,
/// leaving every unlifted hinge's response exactly as the layout carried it.
///
/// The returned [`PartialCurvatureBridgeStep::unlifted`] population is what the
/// caller must read: the successor standing is **not** the carrier's successor
/// wherever that population is nonempty, and the exact discrepancy is the
/// retained increment at the unlifted hinges' endpoints.
pub fn revise_partially(
    standing: &mut LocalStarStanding,
) -> Result<PartialCurvatureBridgeStep, CurvatureBridgeError> {
    let applied = step_partially(standing)?;
    standing.geometry_responses = applied.revised_geometry_responses.clone();
    Ok(applied)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::discrete_curvature::CurvatureHinge;
    use crate::{
        CpuExecutor, EventId, HingeTrajectory, HingeTransportNetwork, HingeUnitSystem,
        HingeWorldLaw, LocalStarLaw, LocalStarMaterial, QuadraticHingeAction, SimplicialComplex,
    };
    use num_traits::Signed;
    use relational_geometry::{integer, rat};

    fn units() -> HingeUnitSystem {
        HingeUnitSystem {
            coordinate: "turn".to_owned(),
            event_step: "event".to_owned(),
            action: "action".to_owned(),
            momentum: "action/turn".to_owned(),
            impulse: "action/turn".to_owned(),
        }
    }

    /// A nonzero vector orthogonal to `edge_vector`.
    fn off_edge(edge_vector: &RatVec3) -> RatVec3 {
        for aux in [
            RatVec3::from_i64(1, 0, 0),
            RatVec3::from_i64(0, 1, 0),
            RatVec3::from_i64(0, 0, 1),
        ] {
            let candidate = edge_vector.cross(&aux);
            if !candidate.norm_squared().is_zero() {
                return candidate;
            }
        }
        panic!("a nonzero edge vector has a nonzero orthogonal complement")
    }

    /// A response direction projecting to exactly `target` along `edge_vector`
    /// and **not parallel to it**.
    ///
    /// The obliqueness is load-bearing and was added after a mutation showed a
    /// fixture defect: with responses parallel to their own edges, "keep the
    /// response's line" and "use the edge's line" are the same line, so a lift
    /// that picked the edge as a canonical direction passed every assertion
    /// about direction. The orthogonal summand is invisible to the projection
    /// — it dots to zero against the edge — and visible to the lift.
    fn response_projecting_to(edge_vector: &RatVec3, target: &Rat) -> RatVec3 {
        edge_vector
            .scale(&(target / edge_vector.norm_squared()))
            .add(&off_edge(edge_vector).scale(&rat(1, 7)))
    }

    /// Assemble a `LocalStarStanding` from a face population, a hinge edge
    /// population, exact positions, and a per-edge target projection.
    fn standing_from(
        complex: SimplicialComplex,
        positions: BTreeMap<VertexId, RatVec3>,
        response: impl Fn(Edge, &RatVec3) -> RatVec3,
    ) -> Result<LocalStarStanding, LocalStarError> {
        let kinematic =
            HingeWorldLaw::new(complex, HingeTransportNetwork::default(), Vec::new()).unwrap();
        let hinges = kinematic.complex.hinges.keys().copied().collect::<Vec<_>>();
        let parameters = hinges
            .iter()
            .map(|hinge| (*hinge, integer(0)))
            .collect::<BTreeMap<_, _>>();
        let kinematic_standing = kinematic.initial_standing(parameters).unwrap();
        let materials = hinges
            .iter()
            .map(|hinge| {
                let edge = kinematic.complex.hinges[hinge].edge;
                let edge_vector = positions[&edge.upper].subtract(&positions[&edge.lower]);
                (
                    *hinge,
                    LocalStarMaterial {
                        action: QuadraticHingeAction::new(integer(2), integer(1), units()).unwrap(),
                        stress_response: rat(1, 4),
                        geometry_response: response(edge, &edge_vector),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let law =
            LocalStarLaw::new(kinematic, materials, Vec::new(), CpuExecutor::serial()).unwrap();
        let trajectories = hinges
            .iter()
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
        law.initial_standing(kinematic_standing, trajectories, positions, Vec::new())
    }

    /// The id of a fixture vertex by the name it was founded under.
    fn named(standing: &LocalStarStanding, name: &str) -> VertexId {
        standing
            .kinematic
            .complex
            .vertices
            .values()
            .find(|vertex| vertex.name == name)
            .expect("the fixture names its vertices")
            .id
    }

    /// Narrow a founded standing's hinge population in place, keeping exactly
    /// the hinges whose edge satisfies `keep`.
    ///
    /// `HingeWorldStanding::complex` documents itself as contemporary incidence
    /// that later topology deeds replace (`simplicial.rs:826-828`), so a
    /// standing carrying fewer hinges than face edges is a value of the public
    /// carrier and not a fabricated one. `initial_standing` cannot produce it —
    /// `face_fields` refuses a face edge without a hinge — which is exactly why
    /// the frames cannot disagree at founding and can disagree afterwards.
    fn retire_hinges(standing: &mut LocalStarStanding, keep: impl Fn(Edge) -> bool) {
        standing
            .kinematic
            .complex
            .hinges
            .retain(|_, hinge| keep(hinge.edge));
    }

    /// Withdraw one face from a founded standing's complex, by the name it was
    /// founded under. The same documented lifecycle as [`retire_hinges`].
    fn retire_face(standing: &mut LocalStarStanding, name: &str) {
        let id = standing
            .kinematic
            .complex
            .faces
            .values()
            .find(|face| face.name == name)
            .expect("the fixture names its faces")
            .id;
        standing.kinematic.complex.faces.remove(&id);
    }

    /// Octahedron: 6 vertices, 8 faces, 12 edges. Every vertex is an interior
    /// cycle of link size 4, so every combinatorial charge is `6 - 4 = 2` and
    /// the discrete Gauss-Bonnet total is `12 = 6 * chi`.
    fn octahedron_complex(
        hinge_edges: impl Fn(Edge) -> bool,
    ) -> (SimplicialComplex, BTreeMap<VertexId, RatVec3>) {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let a = complex.found_vertex("a", founding);
        let b = complex.found_vertex("b", founding);
        let c = complex.found_vertex("c", founding);
        let d = complex.found_vertex("d", founding);
        let e = complex.found_vertex("e", founding);
        let f = complex.found_vertex("f", founding);
        complex.found_face("eab", founding, [e, a, b]).unwrap();
        complex.found_face("ebc", founding, [e, b, c]).unwrap();
        complex.found_face("ecd", founding, [e, c, d]).unwrap();
        complex.found_face("eda", founding, [e, d, a]).unwrap();
        complex.found_face("fba", founding, [f, b, a]).unwrap();
        complex.found_face("fcb", founding, [f, c, b]).unwrap();
        complex.found_face("fdc", founding, [f, d, c]).unwrap();
        complex.found_face("fad", founding, [f, a, d]).unwrap();
        let positions = BTreeMap::from([
            (a, RatVec3::from_i64(-3, -2, 6)),
            (b, RatVec3::from_i64(3, -2, 6)),
            (c, RatVec3::from_i64(0, 3, 7)),
            (d, RatVec3::from_i64(0, -3, 7)),
            (e, RatVec3::from_i64(0, 0, 11)),
            (f, RatVec3::from_i64(0, 0, 3)),
        ]);
        let edges = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        for edge in edges {
            if hinge_edges(edge) {
                complex
                    .found_hinge("octahedral hinge", founding, edge)
                    .unwrap();
            }
        }
        (complex, positions)
    }

    fn octahedron(target: impl Fn(Edge) -> Rat) -> LocalStarStanding {
        let (complex, positions) = octahedron_complex(|_| true);
        standing_from(complex, positions, |edge, vector| {
            response_projecting_to(vector, &target(edge))
        })
        .expect("the octahedron is a well formed standing")
    }

    /// Whether either endpoint of `edge` lies in `vertices`.
    fn touches(edge: Edge, vertices: &[VertexId]) -> bool {
        vertices.contains(&edge.lower) || vertices.contains(&edge.upper)
    }

    /// Pentagonal bipyramid: 7 vertices, 10 faces, 15 edges. TWO distinct link
    /// sizes — the apexes at 5, the equator at 4 — so a fixture built on it can
    /// show that the deficit varies with the link and that the traced deviation
    /// is not the raw deficit. An all-degree-4 fixture cannot.
    fn bipyramid_complex() -> (
        SimplicialComplex,
        BTreeMap<VertexId, RatVec3>,
        [VertexId; 2],
        Vec<VertexId>,
    ) {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let north = complex.found_vertex("north", founding);
        let south = complex.found_vertex("south", founding);
        let equator = (0..5)
            .map(|i| complex.found_vertex(format!("equator-{i}"), founding))
            .collect::<Vec<_>>();
        for i in 0..5 {
            let p = equator[i];
            let q = equator[(i + 1) % 5];
            complex
                .found_face(format!("north-{i}"), founding, [north, p, q])
                .unwrap();
            complex
                .found_face(format!("south-{i}"), founding, [south, q, p])
                .unwrap();
        }
        // Five distinct exact rational points on a closed polygon, plus two
        // apexes off that plane. Nothing here needs to be regular.
        let ring = [
            RatVec3::from_i64(4, 0, 0),
            RatVec3::from_i64(1, 3, 0),
            RatVec3::from_i64(-3, 2, 0),
            RatVec3::from_i64(-2, -3, 0),
            RatVec3::from_i64(2, -4, 0),
        ];
        let mut positions = BTreeMap::from([
            (north, RatVec3::from_i64(0, 0, 5)),
            (south, RatVec3::from_i64(0, 0, -3)),
        ]);
        for (index, vertex) in equator.iter().enumerate() {
            positions.insert(*vertex, ring[index].clone());
        }
        let edges = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        for edge in edges {
            complex
                .found_hinge("bipyramid hinge", founding, edge)
                .unwrap();
        }
        (complex, positions, [north, south], equator)
    }

    fn bipyramid(
        target: impl Fn(Edge, [VertexId; 2]) -> Rat,
    ) -> (LocalStarStanding, [VertexId; 2], Vec<VertexId>) {
        let (complex, positions, apexes, equator) = bipyramid_complex();
        let standing = standing_from(complex, positions, |edge, vector| {
            response_projecting_to(vector, &target(edge, apexes))
        })
        .expect("the bipyramid is a well formed standing");
        (standing, apexes, equator)
    }

    fn touches_apex(edge: Edge, apexes: [VertexId; 2]) -> bool {
        apexes.contains(&edge.lower) || apexes.contains(&edge.upper)
    }

    // ---------------------------------------------------------------
    // The reduction is DOT, and the fixture can tell the difference.
    // ---------------------------------------------------------------

    #[test]
    fn the_projection_separates_an_expanding_hinge_from_a_contracting_one() {
        // Edge {a,b} has vector (6,0,0) and edge {c,d} has vector (0,-6,0):
        // equal `norm_squared`, so a direction-blind reduction cannot tell
        // them apart whatever responses they carry.
        let (complex, positions) = octahedron_complex(|_| true);
        let named_in = |name: &str| {
            complex
                .vertices
                .values()
                .find(|vertex| vertex.name == name)
                .expect("the fixture names its vertices")
                .id
        };
        let (a, b, c, d) = (
            named_in("a"),
            named_in("b"),
            named_in("c"),
            named_in("d"),
        );
        let expanding = Edge::new(a, b).unwrap();
        let contracting = Edge::new(c, d).unwrap();
        assert_eq!(
            positions[&expanding.upper]
                .subtract(&positions[&expanding.lower])
                .norm_squared(),
            positions[&contracting.upper]
                .subtract(&positions[&contracting.lower])
                .norm_squared(),
            "the two hinges must be indistinguishable to a direction-blind \
             reduction, or this test proves nothing about refusing one"
        );

        let standing = octahedron(|edge| {
            if edge == contracting {
                integer(-3)
            } else {
                integer(3)
            }
        });
        let reading = read(&standing).expect("the octahedron conducts");

        let by_edge = |edge: Edge| {
            reading
                .projections
                .values()
                .find(|projection| projection.edge == edge)
                .expect("every octahedral edge is a conducted hinge")
        };
        let up = by_edge(expanding);
        let down = by_edge(contracting);

        assert_eq!(up.along_edge, integer(3));
        assert_eq!(down.along_edge, integer(-3));
        assert!(up.along_edge.is_positive(), "this hinge expands");
        assert!(down.along_edge.is_negative(), "this hinge contracts");
        assert_ne!(up.along_edge, down.along_edge);

        // And the refused reduction cannot separate them.
        assert_eq!(
            up.direction_blind_norm_squared,
            down.direction_blind_norm_squared,
            "`norm_squared` returns the same value for both, which is exactly \
             why the bridge does not use it"
        );
        assert!(!up.direction_blind_norm_squared.is_zero());

        // The signed reduction reaches the deficit: the two vertices of the
        // contracting hinge carry a strictly larger deficit than the rest.
        let deficits = reading.deficits();
        assert_eq!(
            deficits[&c],
            integer(6) - (integer(3) * integer(3) + integer(-3))
        );
        assert_eq!(deficits[&a], integer(6) - integer(12));
        assert_ne!(deficits[&a], deficits[&c]);
    }

    #[test]
    fn the_projection_carries_the_whole_record_and_not_only_the_scalar() {
        let standing = octahedron(|_| integer(3));
        let reading = read(&standing).expect("the octahedron conducts");
        assert_eq!(reading.projections.len(), 12);
        for projection in reading.projections.values() {
            // The vector the layout carries and the vector the layout spends
            // it against both survive the crossing.
            assert_eq!(
                standing.geometry_responses[&projection.hinge],
                projection.response_direction
            );
            assert_eq!(
                standing.spatial.edges[&projection.edge].vector,
                projection.edge_vector
            );
            assert_eq!(
                projection.response_direction.dot(&projection.edge_vector),
                projection.along_edge
            );
            // The retained direction-blind reduction is the RESPONSE's
            // norm-squared. Substituting the edge's would still be
            // direction-blind and would still be equal across the two hinges
            // the test above compares, so only this pins which vector it reads.
            assert_eq!(
                projection.direction_blind_norm_squared,
                projection.response_direction.norm_squared()
            );
            assert_ne!(
                projection.direction_blind_norm_squared,
                projection.edge_vector.norm_squared(),
                "on this fixture the two candidate norms differ at every hinge, \
                 which is what makes the assertion above a measurement"
            );
        }
    }

    // ---------------------------------------------------------------
    // The aperture, and the two frames it declares.
    // ---------------------------------------------------------------

    #[test]
    fn a_closed_surface_conducts_wholly_and_reproduces_the_local_star_charge() {
        let standing = octahedron(|_| integer(1));
        let aperture = declare_aperture(&standing).expect("the octahedron conducts");
        assert_eq!(aperture.conducted.len(), 6);
        assert!(aperture.refused.is_empty());
        assert_eq!(aperture.conducted_hinges.len(), 12);
        assert!(aperture.refused_hinges.is_empty());
        assert!(aperture.porous_vertices().is_empty());

        let defects = standing.coordination_defects().expect("carried");
        for carried in aperture.conducted.values() {
            assert_eq!(
                defects[&carried.vertex],
                LocalCoordinationDefect::InteriorCycle {
                    coordination: 4,
                    charge: 2,
                }
            );
            assert_eq!(carried.incident_hinges, 4);
            assert_eq!(carried.hinge_charge, 2);
            // The negative pole of a two-sided property: the frames agree here
            // and disagree on the narrowed fixture below.
            assert!(carried.frames_agree());
        }

        let reading = read(&standing).expect("the octahedron conducts");
        // Nonzero control: the total is 6 * chi = 12, provably not zero.
        assert_eq!(reading.total_deficit(), integer(12));
        assert!(!reading.total_deficit().is_zero());
        assert!(reading.frame_disagreements().is_empty());
    }

    #[test]
    fn a_narrowed_hinge_population_makes_the_two_coordination_frames_disagree() {
        // Retire the four equatorial hinges. Every vertex keeps its FACE link
        // of four, so `local_star` still reads coordination 4 everywhere, while
        // the equatorial vertices now touch only two hinges. The face frame and
        // the hinge frame therefore return different charges, which no standing
        // straight out of `initial_standing` can exhibit.
        let mut standing = octahedron(|_| rat(9, 4));
        let (a, b, c, d) = (
            named(&standing, "a"),
            named(&standing, "b"),
            named(&standing, "c"),
            named(&standing, "d"),
        );
        let (e, f) = (named(&standing, "e"), named(&standing, "f"));
        retire_hinges(&mut standing, |edge| touches(edge, &[e, f]));
        assert_eq!(standing.kinematic.complex.hinges.len(), 8);

        let reading = read(&standing).expect("the narrowed octahedron still conducts");
        assert_eq!(reading.aperture.conducted.len(), 6);
        assert!(reading.aperture.refused_hinges.is_empty());

        for equatorial in [a, b, c, d] {
            let carried = reading.aperture.conducted[&equatorial];
            assert_eq!(carried.link_coordination, 4, "the FACE link is untouched");
            assert_eq!(carried.incident_hinges, 2, "the HINGE link is narrowed");
            assert_eq!(carried.link_charge, 2);
            assert_eq!(carried.hinge_charge, 4);
            assert!(
                !carried.frames_agree(),
                "vertex {equatorial:?} reads 4 in one frame and 2 in the other"
            );
        }
        for apex in [e, f] {
            let carried = reading.aperture.conducted[&apex];
            assert_eq!(carried.link_coordination, 4);
            assert_eq!(carried.incident_hinges, 4);
            assert!(carried.frames_agree(), "the apexes kept every hinge");
        }

        // The population, not a flag, and it is a proper subpopulation.
        assert_eq!(
            reading
                .frame_disagreements()
                .keys()
                .copied()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([a, b, c, d])
        );

        // And the charge the carrier is told is the HINGE one.
        let charges = reading.combinatorial_charges();
        assert_eq!(charges[&a], 4);
        assert_eq!(charges[&e], 2);
        assert_ne!(
            charges[&a], reading.aperture.conducted[&a].link_charge,
            "reporting the face charge here would be reporting a frame the \
             carrier was never handed"
        );
    }

    #[test]
    fn a_narrowed_hinge_population_reaches_the_nonflat_fixed_point_a_whole_one_cannot() {
        // The retired-equator octahedron IS K(2,4): four vertices of hinge
        // degree 2 against two of hinge degree 4, no odd hinge cycle. At
        // uniform response 9/4 it is `discrete_curvature`'s nonflat fixed
        // point, reached THROUGH the bridge — which this module recorded as
        // structurally impossible until 2026-08-08. What is true is the
        // hinge-closed statement: see the test below.
        let mut standing = octahedron(|_| rat(9, 4));
        let a = named(&standing, "a");
        let (e, f) = (named(&standing, "e"), named(&standing, "f"));
        retire_hinges(&mut standing, |edge| touches(edge, &[e, f]));

        let reading = read(&standing).expect("the narrowed octahedron still conducts");
        assert_eq!(reading.deficits()[&a], rat(3, 2));
        assert_eq!(reading.deficits()[&e], integer(-3));
        assert!(!reading.is_flat());
        for vertex in reading.configuration.vertices() {
            assert!(
                !reading.deficits()[&vertex].is_zero(),
                "vertex {vertex:?} must be charged, or the fixed point is just flat"
            );
        }
        assert!(!reading.configuration.carries_odd_hinge_cycle());
        assert_eq!(reading.configuration.forced_component_scale()[&a], rat(3, 4));
        assert!(matches!(
            reading.fixed_point(),
            CurvatureFixedPoint::AlternatingTracedDeviation { .. }
        ));

        let applied = step(&standing).expect("the narrowed octahedron still conducts");
        assert!(
            !applied.flow.moved,
            "an unbalanced bipartite aperture is FIXED at a nonzero deficit, \
             through the bridge and not only on the bare carrier"
        );
        assert_eq!(
            applied.revised_geometry_responses,
            standing.geometry_responses
        );
        for revision in applied.revisions.values() {
            assert_eq!(revision.magnitude_factor, integer(1));
            assert_eq!(revision.before, revision.after);
        }

        // And the TOTAL deficit here is exactly zero while not one vertex is
        // flat: `4 * 3/2 + 2 * (-3) = 0`. A run grading the total would report
        // convergence on an aperture that is fixed and charged everywhere,
        // which is why the deficit POPULATION is the thing to grade.
        assert!(reading.total_deficit().is_zero());
        assert!(!reading.is_flat());

        // Ten further revisions leave it exactly where it started, and no
        // vertex ever becomes flat.
        let mut carried = standing.clone();
        for _ in 0..10 {
            let applied = revise(&mut carried).expect("the narrowed octahedron conducts");
            assert!(!applied.flow.moved);
            assert!(applied
                .flow
                .deficits_after
                .values()
                .all(|deficit| !deficit.is_zero()));
        }
        assert_eq!(carried.geometry_responses, standing.geometry_responses);
    }

    #[test]
    fn an_interior_cycle_carrying_no_hinge_is_refused_by_name() {
        // Retire the eight spokes. The apexes keep their face link of four and
        // lose every hinge, so they are interior cycles with `n_v = 0`: the
        // traced deviation is undefined and the aperture must say why rather
        // than hand the carrier a vertex it will call isolated.
        let mut standing = octahedron(|_| integer(1));
        let (a, b, c, d) = (
            named(&standing, "a"),
            named(&standing, "b"),
            named(&standing, "c"),
            named(&standing, "d"),
        );
        let (e, f) = (named(&standing, "e"), named(&standing, "f"));
        retire_hinges(&mut standing, |edge| !touches(edge, &[e, f]));
        assert_eq!(standing.kinematic.complex.hinges.len(), 4);

        let aperture = declare_aperture(&standing).expect("the equatorial ring still conducts");
        assert_eq!(
            aperture.refused,
            BTreeMap::from([
                (e, ApertureRefusal::InteriorCycleWithoutHinges),
                (f, ApertureRefusal::InteriorCycleWithoutHinges),
            ])
        );
        assert_eq!(
            aperture.conducted.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([a, b, c, d])
        );
        assert_eq!(aperture.conducted_hinges.len(), 4);
        assert!(aperture.refused_hinges.is_empty());

        // Both refusal species carry: the standing still reads and moves.
        let reading = read(&standing).expect("the equatorial ring conducts");
        assert_eq!(reading.deficits()[&a], integer(4));
        assert!(step(&standing).expect("it conducts").flow.moved);
    }

    #[test]
    fn a_standing_carrying_no_conducted_vertex_refuses_the_whole_aperture() {
        let mut standing = octahedron(|_| integer(1));
        retire_hinges(&mut standing, |_| false);
        assert!(standing.kinematic.complex.hinges.is_empty());
        assert_eq!(
            declare_aperture(&standing),
            Err(CurvatureBridgeError::EmptyAperture)
        );
        assert_eq!(read(&standing), Err(CurvatureBridgeError::EmptyAperture));
    }

    #[test]
    fn a_withheld_face_leaves_a_boundary_path_the_aperture_refuses_by_name() {
        // Withdraw face `eab`. Vertices a, b and e then carry PATH links, which
        // has no `6 - |link|` doctrine at `local_star.rs:1151`. `initial_standing`
        // cannot produce this — a boundary edge has one coface and can carry no
        // hinge, so `face_fields` refuses — but a later topology deed can, and
        // `ApertureRefusal::BoundaryPath` is the arm that receives it.
        let mut standing = octahedron(|_| integer(1));
        retire_face(&mut standing, "eab");
        let (a, b, e) = (
            named(&standing, "a"),
            named(&standing, "b"),
            named(&standing, "e"),
        );
        let defects = standing.coordination_defects().expect("carried");
        assert_eq!(
            defects[&e],
            LocalCoordinationDefect::BoundaryPath { coordination: 4 }
        );

        let aperture = declare_aperture(&standing).expect("c, d and f still conduct");
        for boundary in [a, b, e] {
            assert_eq!(
                aperture.refused[&boundary],
                ApertureRefusal::BoundaryPath { coordination: 4 },
                "vertex {boundary:?} lost its cycle link with the face"
            );
        }
        assert_eq!(aperture.refused.len(), 3);
        assert_eq!(aperture.conducted.len(), 3);

        // Every conducted vertex now leaks a hinge into the boundary, so the
        // reading refuses with the leak population rather than under-counting.
        match read(&standing) {
            Err(CurvatureBridgeError::AperturePorous { leaks }) => {
                assert_eq!(leaks.len(), 3);
            }
            other => panic!("expected a porosity refusal, got {other:?}"),
        }
    }

    /// Two octahedra sharing exactly one vertex, plus one vertex in no face.
    ///
    /// The shared vertex has a link of two disjoint cycles, so `local_star`
    /// classes it `Singular`; the free vertex is `Isolated`. Every other vertex
    /// is an interior cycle, and the eight of them adjacent to the pinch each
    /// lose one hinge to it, so the aperture is porous.
    fn pinched_octahedra() -> (LocalStarStanding, [VertexId; 12]) {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let a = complex.found_vertex("a", founding);
        let b = complex.found_vertex("b", founding);
        let c = complex.found_vertex("c", founding);
        let d = complex.found_vertex("d", founding);
        let e = complex.found_vertex("e", founding);
        let f = complex.found_vertex("f", founding);
        let g = complex.found_vertex("g", founding);
        let h = complex.found_vertex("h", founding);
        let i = complex.found_vertex("i", founding);
        let j = complex.found_vertex("j", founding);
        let k = complex.found_vertex("k", founding);
        let free = complex.found_vertex("free", founding);
        for (name, vertices) in [
            ("eab", [e, a, b]),
            ("ebc", [e, b, c]),
            ("ecd", [e, c, d]),
            ("eda", [e, d, a]),
            ("fba", [f, b, a]),
            ("fcb", [f, c, b]),
            ("fdc", [f, d, c]),
            ("fad", [f, a, d]),
            ("kgh", [k, g, h]),
            ("khi", [k, h, i]),
            ("kij", [k, i, j]),
            ("kjg", [k, j, g]),
            ("fhg", [f, h, g]),
            ("fih", [f, i, h]),
            ("fji", [f, j, i]),
            ("fgj", [f, g, j]),
        ] {
            complex.found_face(name, founding, vertices).unwrap();
        }
        let positions = BTreeMap::from([
            (a, RatVec3::from_i64(-3, -2, 6)),
            (b, RatVec3::from_i64(3, -2, 6)),
            (c, RatVec3::from_i64(0, 3, 7)),
            (d, RatVec3::from_i64(0, -3, 7)),
            (e, RatVec3::from_i64(0, 0, 11)),
            (f, RatVec3::from_i64(0, 0, 3)),
            (g, RatVec3::from_i64(-3, -2, -4)),
            (h, RatVec3::from_i64(3, -2, -4)),
            (i, RatVec3::from_i64(0, 3, -5)),
            (j, RatVec3::from_i64(0, -3, -5)),
            (k, RatVec3::from_i64(0, 0, -9)),
            (free, RatVec3::from_i64(20, 20, 20)),
        ]);
        let edges = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        for edge in edges {
            complex
                .found_hinge("pinched hinge", founding, edge)
                .unwrap();
        }
        let standing = standing_from(complex, positions, |_, vector| {
            response_projecting_to(vector, &integer(1))
        })
        .expect("a pinched pair of closed octahedra is a well formed standing");
        (standing, [a, b, c, d, e, f, g, h, i, j, k, free])
    }

    #[test]
    fn a_singular_link_an_isolated_vertex_and_a_porous_interior_are_typed_refusals() {
        let (standing, [a, b, c, d, e, f, g, h, i, j, k, free]) = pinched_octahedra();
        assert_eq!(standing.kinematic.complex.hinges.len(), 24);

        let aperture = declare_aperture(&standing).expect("ten vertices still conduct");
        // Both halves populated, so neither branch passes vacuously.
        assert_eq!(
            aperture.conducted.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([a, b, c, d, e, g, h, i, j, k])
        );
        assert_eq!(
            aperture.refused,
            BTreeMap::from([
                (f, ApertureRefusal::SingularLink { coordination: 8 }),
                (free, ApertureRefusal::IsolatedLink),
            ])
        );
        assert_eq!(aperture.conducted_hinges.len(), 16);
        assert_eq!(aperture.refused_hinges.len(), 8);
        for refused in aperture.refused_hinges.values() {
            assert_eq!(refused.exterior, f);
        }

        // The eight equator vertices leak one hinge each into the pinch; the
        // two apexes do not leak at all, so the population distinguishes them.
        let leaks = aperture.porous_vertices();
        assert_eq!(
            leaks.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([a, b, c, d, g, h, i, j])
        );
        for leak in leaks.values() {
            assert_eq!(leak.incident_in_complex, 4);
            assert_eq!(leak.incident_in_aperture, 3);
        }
        assert!(!leaks.contains_key(&e));
        assert!(!leaks.contains_key(&k));

        // And the reading refuses with the WHOLE population, not the one vertex
        // the carrier happens to name first.
        assert_eq!(read(&standing), Err(CurvatureBridgeError::AperturePorous { leaks }));
    }

    #[test]
    fn the_carriers_own_incidence_certification_is_a_second_frame_on_the_leak_population() {
        // The bridge establishes porosity from its own aperture. `found`
        // establishes the same fact independently, by comparing the declared
        // link size against the incidence of the hinges it is handed. Hand it
        // the porous aperture directly and require the two to agree.
        let (standing, _) = pinched_octahedra();
        let aperture = declare_aperture(&standing).expect("ten vertices conduct");
        let leaks = aperture.porous_vertices();
        assert!(!leaks.is_empty());

        let complex = &standing.kinematic.complex;
        let projections =
            project_responses(&standing, &aperture).expect("every conducted hinge projects");
        let refused = DiscreteCurvatureConfiguration::found(
            aperture
                .conducted
                .values()
                .map(|carried| (carried.vertex, carried.incident_hinges)),
            projections.values().map(|projection| {
                let edge = complex.hinges[&projection.hinge].edge;
                (
                    projection.hinge,
                    [edge.lower, edge.upper],
                    projection.along_edge.clone(),
                )
            }),
        )
        .expect_err("the carrier must refuse the porous aperture too");

        match refused {
            DiscreteCurvatureError::DeclaredLinkSizeDisagreesWithIncidence {
                vertex,
                declared,
                incident,
            } => {
                let leak = leaks
                    .get(&vertex)
                    .expect("the carrier named a vertex the bridge did not call porous");
                assert_eq!(leak.incident_in_complex, declared);
                assert_eq!(leak.incident_in_aperture, incident);
            }
            other => panic!("expected an incidence disagreement, got {other:?}"),
        }
    }

    #[test]
    fn a_conducted_vertex_whose_every_hinge_is_refused_reports_porosity() {
        // `found` checks `incident == 0` BEFORE it compares the declared count,
        // so a conducted vertex all of whose hinges leak used to surface as
        // `Carrier(IsolatedVertex)` — the wrong refusal, naming the wrong
        // organ. Retire three of `a`'s four hinges so its only remaining one
        // runs into the singular pinch.
        let (mut standing, [a, _, _, _, _, f, ..]) = pinched_octahedra();
        retire_hinges(&mut standing, |edge| {
            let touches_a = edge.lower == a || edge.upper == a;
            !touches_a || edge.lower == f || edge.upper == f
        });
        assert_eq!(
            standing
                .kinematic
                .complex
                .hinges
                .values()
                .filter(|hinge| hinge.edge.lower == a || hinge.edge.upper == a)
                .count(),
            1
        );

        let aperture = declare_aperture(&standing).expect("the rest still conducts");
        let leaks = aperture.porous_vertices();
        assert_eq!(
            leaks[&a],
            ApertureLeak {
                vertex: a,
                incident_in_complex: 1,
                incident_in_aperture: 0,
            }
        );
        assert!(
            leaks.len() > 1,
            "the population must carry more than the total-loss vertex"
        );
        assert_eq!(read(&standing), Err(CurvatureBridgeError::AperturePorous { leaks }));

        // And this is exactly the case the carrier would have called isolated.
        let projections =
            project_responses(&standing, &aperture).expect("every conducted hinge projects");
        let complex = &standing.kinematic.complex;
        let refused = DiscreteCurvatureConfiguration::found(
            aperture
                .conducted
                .values()
                .map(|carried| (carried.vertex, carried.incident_hinges)),
            projections.values().map(|projection| {
                let edge = complex.hinges[&projection.hinge].edge;
                (
                    projection.hinge,
                    [edge.lower, edge.upper],
                    projection.along_edge.clone(),
                )
            }),
        )
        .expect_err("the carrier refuses this aperture too");
        assert_eq!(refused, DiscreteCurvatureError::IsolatedVertex(a));
    }

    /// Two octahedra sharing two ADJACENT vertices as their apexes.
    ///
    /// `a` and `b` each carry two disjoint cycle links, so both are `Singular`,
    /// and the edge `{a,b}` between them — a face edge of the first octahedron
    /// with exactly two cofaces — is a hinge **both** of whose endpoints lie
    /// outside the aperture. That is the only way to reach a refused hinge that
    /// does not also make some conducted vertex porous.
    fn spheres_joined_at_an_edge() -> (LocalStarStanding, [VertexId; 10]) {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let a = complex.found_vertex("a", founding);
        let b = complex.found_vertex("b", founding);
        let c = complex.found_vertex("c", founding);
        let d = complex.found_vertex("d", founding);
        let e = complex.found_vertex("e", founding);
        let f = complex.found_vertex("f", founding);
        let p = complex.found_vertex("p", founding);
        let q = complex.found_vertex("q", founding);
        let r = complex.found_vertex("r", founding);
        let s = complex.found_vertex("s", founding);
        for (name, vertices) in [
            ("eab", [e, a, b]),
            ("ebc", [e, b, c]),
            ("ecd", [e, c, d]),
            ("eda", [e, d, a]),
            ("fba", [f, b, a]),
            ("fcb", [f, c, b]),
            ("fdc", [f, d, c]),
            ("fad", [f, a, d]),
            ("apq", [a, p, q]),
            ("aqr", [a, q, r]),
            ("ars", [a, r, s]),
            ("asp", [a, s, p]),
            ("bqp", [b, q, p]),
            ("brq", [b, r, q]),
            ("bsr", [b, s, r]),
            ("bps", [b, p, s]),
        ] {
            complex.found_face(name, founding, vertices).unwrap();
        }
        let positions = BTreeMap::from([
            (a, RatVec3::from_i64(-3, -2, 6)),
            (b, RatVec3::from_i64(3, -2, 6)),
            (c, RatVec3::from_i64(0, 3, 7)),
            (d, RatVec3::from_i64(0, -3, 7)),
            (e, RatVec3::from_i64(0, 0, 11)),
            (f, RatVec3::from_i64(0, 0, 3)),
            (p, RatVec3::from_i64(-4, -6, -2)),
            (q, RatVec3::from_i64(4, -6, -3)),
            (r, RatVec3::from_i64(5, -9, -6)),
            (s, RatVec3::from_i64(-5, -8, -7)),
        ]);
        let edges = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        for edge in edges {
            complex.found_hinge("joined hinge", founding, edge).unwrap();
        }
        let standing = standing_from(complex, positions, |_, vector| {
            response_projecting_to(vector, &integer(1))
        })
        .expect("two spheres joined at an edge is a well formed standing");
        (standing, [a, b, c, d, e, f, p, q, r, s])
    }

    #[test]
    fn a_refused_hinge_outside_a_conducting_aperture_is_carried_verbatim_into_the_successor() {
        let (mut standing, [a, b, ..]) = spheres_joined_at_an_edge();
        assert_eq!(standing.kinematic.complex.hinges.len(), 24);
        let founding_responses = standing.geometry_responses.clone();

        // Every hinge touching a or b except {a,b} itself would make some
        // conducted vertex porous; retire exactly those. What remains is a
        // conducting aperture PLUS one refused hinge, which no whole-hinge
        // standing can present.
        retire_hinges(&mut standing, |edge| {
            let joins_the_pinch = (edge.lower == a && edge.upper == b)
                || (edge.lower == b && edge.upper == a);
            let touches_the_pinch =
                [edge.lower, edge.upper].iter().any(|v| *v == a || *v == b);
            joins_the_pinch || !touches_the_pinch
        });
        assert_eq!(standing.kinematic.complex.hinges.len(), 10);

        let aperture = declare_aperture(&standing).expect("eight vertices conduct");
        assert_eq!(
            aperture.refused,
            BTreeMap::from([
                (a, ApertureRefusal::SingularLink { coordination: 8 }),
                (b, ApertureRefusal::SingularLink { coordination: 8 }),
            ])
        );
        assert_eq!(aperture.conducted.len(), 8);
        assert_eq!(aperture.conducted_hinges.len(), 9);
        assert_eq!(aperture.refused_hinges.len(), 1);
        let (pinch, refused_hinge) = aperture
            .refused_hinges
            .iter()
            .next()
            .expect("the joining hinge is refused");
        assert_eq!(refused_hinge.edge, Edge::new(a, b).unwrap());
        assert_eq!(
            refused_hinge.exterior, a,
            "both endpoints are outside, so the lower one is named"
        );
        assert!(
            aperture.porous_vertices().is_empty(),
            "no conducted vertex touches the refused hinge, which is what lets \
             the reading succeed while a refusal stands"
        );

        let applied = step(&standing).expect("the joined spheres conduct");
        assert!(applied.flow.moved);
        assert_eq!(applied.revisions.len(), 9);

        // THE POINT: the successor population is complete. Every conducted
        // hinge moved and every hinge outside the aperture — the refused one
        // and the fourteen retired ones — is carried verbatim.
        assert_eq!(
            applied.revised_geometry_responses.len(),
            founding_responses.len()
        );
        assert_eq!(
            applied.revised_geometry_responses[pinch], founding_responses[pinch],
            "the refused hinge's response must cross unchanged"
        );
        for (hinge, response) in &founding_responses {
            if aperture.conducted_hinges.contains(hinge) {
                assert_ne!(
                    &applied.revised_geometry_responses[hinge], response,
                    "conducted hinge {hinge:?} did not move"
                );
            } else {
                assert_eq!(
                    &applied.revised_geometry_responses[hinge], response,
                    "hinge {hinge:?} is outside the aperture and must be verbatim"
                );
            }
        }
    }

    #[test]
    fn a_missing_response_and_a_missing_edge_vector_are_typed_refusals() {
        let standing = octahedron(|_| integer(1));
        let conducted = *declare_aperture(&standing)
            .expect("the octahedron conducts")
            .conducted_hinges
            .iter()
            .next()
            .expect("it carries hinges");
        let edge = standing.kinematic.complex.hinges[&conducted].edge;

        let mut without_response = standing.clone();
        without_response.geometry_responses.remove(&conducted);
        assert_eq!(
            read(&without_response),
            Err(CurvatureBridgeError::MissingGeometryResponse { hinge: conducted })
        );

        let mut without_edge = standing.clone();
        without_edge.spatial.edges.remove(&edge);
        assert_eq!(
            read(&without_edge),
            Err(CurvatureBridgeError::MissingSpatialEdge {
                hinge: conducted,
                edge,
            })
        );
    }

    #[test]
    fn a_standing_cannot_withhold_a_hinge_from_a_face_edge() {
        // The recorded reason the two coordination frames cannot disagree AT
        // FOUNDING, which is what makes the narrowed fixtures above the only
        // material on which they can. `face_fields` requires a hinge on every
        // face boundary edge and `found_hinge` requires exactly two cofaces, so
        // every FOUNDED standing is a closed surface: hinge incidence at a
        // vertex IS its link cardinality, and no vertex can have a path link.
        let (spoked, positions) = octahedron_complex(|edge| {
            // Withhold the equator hinges, keeping only the spokes to e and f.
            let ids = [edge.lower.0, edge.upper.0];
            ids.contains(&5) || ids.contains(&6)
        });
        assert_eq!(spoked.hinges.len(), 8);
        let refusal = standing_from(spoked, positions, |_, vector| {
            response_projecting_to(vector, &rat(9, 4))
        });
        assert!(
            matches!(refusal, Err(LocalStarError::MissingBoundaryHinge(_))),
            "expected a boundary-hinge refusal, got {refusal:?}"
        );

        // The same refusal blocks a boundary outright: withholding face `eab`
        // leaves three face edges with one coface, which can carry no hinge.
        let founding = EventId(1);
        let mut punctured = SimplicialComplex::default();
        let a = punctured.found_vertex("a", founding);
        let b = punctured.found_vertex("b", founding);
        let c = punctured.found_vertex("c", founding);
        let d = punctured.found_vertex("d", founding);
        let e = punctured.found_vertex("e", founding);
        let f = punctured.found_vertex("f", founding);
        for (name, vertices) in [
            ("ebc", [e, b, c]),
            ("ecd", [e, c, d]),
            ("eda", [e, d, a]),
            ("fba", [f, b, a]),
            ("fcb", [f, c, b]),
            ("fdc", [f, d, c]),
            ("fad", [f, a, d]),
        ] {
            punctured.found_face(name, founding, vertices).unwrap();
        }
        let edges = punctured
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        for edge in edges {
            let _ = punctured.found_hinge("octahedral hinge", founding, edge);
        }
        assert_eq!(
            punctured.hinges.len(),
            9,
            "the three edges of the withheld face carry no hinge"
        );
        let punctured_positions = BTreeMap::from([
            (a, RatVec3::from_i64(-3, -2, 6)),
            (b, RatVec3::from_i64(3, -2, 6)),
            (c, RatVec3::from_i64(0, 3, 7)),
            (d, RatVec3::from_i64(0, -3, 7)),
            (e, RatVec3::from_i64(0, 0, 11)),
            (f, RatVec3::from_i64(0, 0, 3)),
        ]);
        let refusal = standing_from(punctured, punctured_positions, |_, vector| {
            response_projecting_to(vector, &integer(1))
        });
        assert!(
            matches!(refusal, Err(LocalStarError::MissingBoundaryHinge(_))),
            "expected a boundary-hinge refusal, got {refusal:?}"
        );
    }

    // ---------------------------------------------------------------
    // FALSIFIER: a charged layout MUST move.
    // ---------------------------------------------------------------

    #[test]
    fn a_charged_layout_moves_and_every_response_is_revised() {
        let standing = octahedron(|_| integer(1));
        let reading = read(&standing).expect("the octahedron conducts");

        // Nonzero control: every vertex is charged, and by exactly 2.
        for vertex in standing.kinematic.complex.vertices.keys() {
            assert_eq!(reading.deficits()[vertex], integer(2));
        }
        assert_eq!(reading.total_deficit(), integer(12));
        assert!(matches!(
            reading.fixed_point(),
            CurvatureFixedPoint::Moving { .. }
        ));

        let applied = step(&standing).expect("the octahedron conducts");
        assert!(applied.flow.moved);
        assert_eq!(applied.revisions.len(), 12);

        // h(v) = 2/4 = 1/2 everywhere, so every hinge is revised by exactly 1.
        for revision in applied.revisions.values() {
            assert_eq!(revision.along_edge_before, integer(1));
            assert_eq!(revision.along_edge_after, integer(2));
            assert_eq!(revision.magnitude_factor, integer(2));
            assert_ne!(revision.before, revision.after);
            assert!(!revision.along_edge_after.is_zero());
        }

        // The write-back reaches the standing's own carrier type.
        for (hinge, response) in &applied.revised_geometry_responses {
            assert_ne!(
                response, &standing.geometry_responses[hinge],
                "hinge {hinge:?} did not move"
            );
        }

        // And the revised layout reads back with the successor deficits.
        let mut moved = standing.clone();
        let again = revise(&mut moved).expect("the octahedron conducts");
        assert_eq!(again.revised_geometry_responses, moved.geometry_responses);
        let after = read(&moved).expect("the octahedron conducts");
        assert_eq!(after.deficits(), applied.flow.deficits_after);
        for vertex in moved.kinematic.complex.vertices.keys() {
            assert_eq!(after.deficits()[vertex], integer(-2));
        }
    }

    // ---------------------------------------------------------------
    // FALSIFIER: a flat layout MUST stay exactly fixed.
    // ---------------------------------------------------------------

    #[test]
    fn a_flat_layout_is_left_exactly_fixed() {
        // Apex hinges project to 6/5, equator hinges to 9/5. Apex deficit is
        // 6 - 5*(6/5) = 0; equator deficit is 6 - (2*(6/5) + 2*(9/5)) = 0.
        // TWO link sizes and TWO response values, so this fixture could have
        // moved: flatness here is a property of the layout, not of uniformity.
        let (standing, apexes, equator) = bipyramid(|edge, apexes| {
            if touches_apex(edge, apexes) {
                rat(6, 5)
            } else {
                rat(9, 5)
            }
        });
        let reading = read(&standing).expect("the bipyramid conducts");

        let link_sizes = reading
            .aperture
            .conducted
            .values()
            .map(|carried| carried.incident_hinges)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            link_sizes,
            BTreeSet::from([4, 5]),
            "the fixture must carry more than one link size"
        );
        let projected = reading
            .projections
            .values()
            .map(|projection| projection.along_edge.clone())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            projected,
            BTreeSet::from([rat(6, 5), rat(9, 5)]),
            "the fixture must carry more than one projected response"
        );
        assert_eq!(reading.aperture.conducted.len(), 7);
        assert_eq!(reading.aperture.conducted_hinges.len(), 15);
        for apex in apexes {
            assert_eq!(reading.aperture.conducted[&apex].incident_hinges, 5);
        }
        for vertex in &equator {
            assert_eq!(reading.aperture.conducted[vertex].incident_hinges, 4);
        }

        assert!(reading.is_flat());
        assert_eq!(reading.total_deficit(), Rat::zero());
        assert_eq!(reading.fixed_point(), CurvatureFixedPoint::Flat);

        let applied = step(&standing).expect("the bipyramid conducts");
        assert!(
            !applied.flow.moved,
            "a bridge that moves a flat layout is introducing curvature rather \
             than responding to it"
        );
        for revision in applied.revisions.values() {
            assert_eq!(revision.magnitude_factor, integer(1));
            assert_eq!(revision.before, revision.after);
            assert_eq!(revision.along_edge_before, revision.along_edge_after);
        }
        assert_eq!(
            applied.revised_geometry_responses,
            standing.geometry_responses
        );

        // Ten further revisions change nothing at all.
        let mut carried = standing.clone();
        for _ in 0..10 {
            let applied = revise(&mut carried).expect("the bipyramid conducts");
            assert!(!applied.flow.moved);
        }
        assert_eq!(carried.geometry_responses, standing.geometry_responses);
    }

    #[test]
    fn a_charged_bipyramid_moves_although_a_flat_one_does_not() {
        // The same fixture at unit projection: apex deficit 1, equator deficit
        // 2, so the two link sizes produce two different traced deviations and
        // the revisions are not all equal.
        let (standing, apexes, equator) = bipyramid(|_, _| integer(1));
        let reading = read(&standing).expect("the bipyramid conducts");
        for apex in apexes {
            assert_eq!(reading.deficits()[&apex], integer(1));
        }
        for vertex in &equator {
            assert_eq!(reading.deficits()[vertex], integer(2));
        }
        assert_eq!(reading.total_deficit(), integer(12));

        let applied = step(&standing).expect("the bipyramid conducts");
        assert!(applied.flow.moved);
        let increments = applied
            .revisions
            .values()
            .map(|revision| &revision.along_edge_after - &revision.along_edge_before)
            .collect::<BTreeSet<_>>();
        // Apex hinges 1/5 + 1/2 = 7/10; equator hinges 1/2 + 1/2 = 1.
        assert_eq!(increments, BTreeSet::from([rat(7, 10), integer(1)]));
        assert!(
            increments.len() > 1,
            "a fixture whose revisions are all equal cannot show the traced \
             deviation depends on the link size"
        );
    }

    // ---------------------------------------------------------------
    // FALSIFIER: grade the DEFICIT, not the combinatorial charge.
    // ---------------------------------------------------------------

    #[test]
    fn the_combinatorial_charge_is_fixed_while_the_deficit_moves() {
        let mut standing = octahedron(|_| integer(1));
        let founding_charges = read(&standing)
            .expect("the octahedron conducts")
            .combinatorial_charges();
        assert_eq!(
            founding_charges.values().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([2])
        );

        let mut deficits = vec![read(&standing).expect("conducts").deficits()];
        for _ in 0..5 {
            let applied = revise(&mut standing).expect("the octahedron conducts");
            assert!(applied.flow.moved, "the deficit is moving at every step");
            let reading = read(&standing).expect("the octahedron conducts");
            assert_eq!(
                reading.combinatorial_charges(),
                founding_charges,
                "the charge cannot move while the complex is fixed, which is \
                 exactly why grading a flow step by it concludes wrongly"
            );
            deficits.push(reading.deficits());
        }

        // The deficit population genuinely varies across the run.
        let distinct = deficits
            .iter()
            .map(|population| population.values().cloned().collect::<Vec<_>>())
            .collect::<BTreeSet<_>>();
        assert!(
            distinct.len() >= 2,
            "the deficit must actually vary, or grading it proves nothing either"
        );
        assert_eq!(deficits[0].values().next().unwrap(), &integer(2));
        assert_eq!(deficits[1].values().next().unwrap(), &integer(-2));
    }

    // ---------------------------------------------------------------
    // FALSIFIER: "the flow drives every deficit to zero" is FALSE.
    // ---------------------------------------------------------------

    #[test]
    fn the_flow_does_not_drive_the_deficit_to_zero_it_negates_it_forever() {
        let mut standing = octahedron(|_| integer(1));
        let mut totals = vec![read(&standing).expect("conducts").total_deficit()];
        for _ in 0..8 {
            let applied = revise(&mut standing).expect("the octahedron conducts");
            assert_eq!(
                applied.flow.total_deficit_after,
                -applied.flow.total_deficit_before.clone(),
                "one step negates the total exactly"
            );
            totals.push(applied.flow.total_deficit_after.clone());
        }
        assert_eq!(
            totals,
            vec![
                integer(12),
                integer(-12),
                integer(12),
                integer(-12),
                integer(12),
                integer(-12),
                integer(12),
                integer(-12),
                integer(12),
            ]
        );
        for total in &totals {
            assert!(
                !total.is_zero(),
                "the total deficit is never zero, so no run may claim the flow \
                 drives it there"
            );
            assert_eq!(total.abs(), integer(12));
        }
    }

    #[test]
    fn a_hinge_closed_aperture_carries_an_odd_cycle_and_can_only_be_fixed_when_flat() {
        // The correct, BOUNDED form of the claim this module used to make about
        // nonflat fixed points. It is a statement about apertures closed under
        // hinge incidence; the narrowed fixture above shows it is false without
        // that hypothesis, which is why the hypothesis is named here.
        for standing in [
            octahedron(|_| integer(1)),
            bipyramid(|_, _| integer(1)).0,
            octahedron(|_| rat(7, 3)),
        ] {
            let reading = read(&standing).expect("the fixture conducts");
            assert!(
                reading.configuration.carries_odd_hinge_cycle(),
                "a hinge-closed interior-cycle aperture contains a whole triangle"
            );
            for scale in reading.configuration.forced_component_scale().values() {
                assert!(
                    scale.is_zero(),
                    "an odd-cycle component forces the scale to zero, so flat \
                     is the only fixed configuration such an aperture presents"
                );
            }
            assert_eq!(
                matches!(reading.fixed_point(), CurvatureFixedPoint::Flat),
                reading.is_flat(),
                "fixed if and only if flat, on every hinge-closed aperture"
            );
        }
    }

    // ---------------------------------------------------------------
    // The lift, and what it refuses.
    // ---------------------------------------------------------------

    #[test]
    fn the_lift_keeps_the_line_and_certifies_the_scalar_it_was_asked_for() {
        // Varied targets, so neither the factors nor the directions are equal
        // across the population.
        let (standing, _, _) = bipyramid(|edge, apexes| {
            if touches_apex(edge, apexes) {
                rat(3, 2)
            } else {
                rat(-5, 4)
            }
        });
        let applied = step(&standing).expect("the bipyramid conducts");
        assert_eq!(applied.revisions.len(), 15);

        let factors = applied
            .revisions
            .values()
            .map(|revision| revision.magnitude_factor.clone())
            .collect::<BTreeSet<_>>();
        assert!(
            factors.len() >= 2,
            "the fixture must produce distinct magnitude factors, got {factors:?}"
        );

        for revision in applied.revisions.values() {
            let edge_vector = &standing.spatial.edges[&revision.edge].vector;
            // The fixture must be OBLIQUE, or "keep the response's line" and
            // "use the edge's line" are the same line and this test cannot see
            // a lift that invented a canonical direction.
            assert_ne!(
                revision.before.cross(edge_vector),
                RatVec3::zero(),
                "hinge {:?} carries a response parallel to its own edge, which \
                 makes the direction claim untestable there",
                revision.hinge
            );
            // The certificate: the lift returns exactly the scalar it was given.
            assert_eq!(revision.after.dot(edge_vector), revision.along_edge_after);
            // The line is carried verbatim: `after` is a rational multiple of
            // `before`, so their cross product vanishes exactly.
            assert_eq!(revision.after.cross(&revision.before), RatVec3::zero());
            // And it is NOT the edge's line, so a lift that reconstructed the
            // response from the edge would be visible here.
            assert_ne!(revision.after.cross(edge_vector), RatVec3::zero());
            assert_eq!(
                revision.before.scale(&revision.magnitude_factor),
                revision.after
            );
            // PROVENANCE, replacing an assertion deleted 2026-08-08. The old
            // line asserted `magnitude_factor * along_edge_before ==
            // along_edge_after`, which is `(a/b)*b == a` over a field and could
            // not have come out otherwise. What can come out otherwise is where
            // the requested scalar came from: it must be the projection plus the
            // CARRIER's own increment for that hinge.
            assert_eq!(
                revision.along_edge_after,
                &revision.along_edge_before + &applied.flow.revisions[&revision.hinge]
            );
            // Nonzero control: the response actually points somewhere.
            assert!(!revision.before.norm_squared().is_zero());
        }
    }

    /// An octahedron at unit projection with the responses on `{a,b}` and
    /// `{c,d}` turned exactly orthogonal to their own edges. Reading still
    /// succeeds — the carrier simply receives a zero response there — and both
    /// hinges are unliftable, so a refusal that returns only the first one is
    /// visibly short.
    fn octahedron_with_two_orthogonal_responses() -> (LocalStarStanding, [HingeId; 2]) {
        let mut standing = octahedron(|_| integer(1));
        let (a, b, c, d) = (
            named(&standing, "a"),
            named(&standing, "b"),
            named(&standing, "c"),
            named(&standing, "d"),
        );
        let mut turned = Vec::new();
        for edge in [Edge::new(a, b).unwrap(), Edge::new(c, d).unwrap()] {
            let hinge = standing
                .kinematic
                .complex
                .hinges
                .values()
                .find(|hinge| hinge.edge == edge)
                .expect("the fixture carries a hinge on every edge")
                .id;
            let edge_vector = standing.spatial.edges[&edge].vector.clone();
            let sideways = edge_vector.cross(&RatVec3::from_i64(1, 1, 1));
            assert!(
                !sideways.norm_squared().is_zero(),
                "the constructed orthogonal response must not be the zero vector"
            );
            assert!(sideways.dot(&edge_vector).is_zero());
            standing.geometry_responses.insert(hinge, sideways);
            turned.push(hinge);
        }
        (standing, [turned[0], turned[1]])
    }

    #[test]
    fn the_lift_refuses_every_response_that_spends_nothing_along_its_own_edge() {
        let (standing, [first, second]) = octahedron_with_two_orthogonal_responses();
        let untouched = standing.geometry_responses.clone();
        let reading = read(&standing).expect("the reading still succeeds");
        for hinge in [first, second] {
            let projection = &reading.projections[&hinge];
            assert!(projection.along_edge.is_zero());
            // And the refused reduction would NOT have been zero, which is the
            // whole content of preferring the signed one.
            assert!(!projection.direction_blind_norm_squared.is_zero());
        }

        match step(&standing) {
            Err(CurvatureBridgeError::ResponsesOrthogonalToTheirOwnEdges { refused }) => {
                assert_eq!(
                    refused.keys().copied().collect::<BTreeSet<_>>(),
                    BTreeSet::from([first, second]),
                    "the refusal must carry EVERY unliftable hinge, not the \
                     first one the traversal reached"
                );
                for hinge in [first, second] {
                    let record = &refused[&hinge];
                    assert_eq!(
                        record.requested,
                        rat(3, 2),
                        "the refusal must carry the scalar it could not reach"
                    );
                    assert!(!record.requested.is_zero());
                    assert_eq!(
                        record.response_direction,
                        standing.geometry_responses[&hinge],
                        "the refusal carries the geometry, not only the name"
                    );
                    assert!(record
                        .response_direction
                        .dot(&record.edge_vector)
                        .is_zero());
                }
            }
            other => panic!("expected an orthogonality refusal, got {other:?}"),
        }
        // The standing was not touched.
        assert_eq!(standing.geometry_responses, untouched);
    }

    #[test]
    fn the_partial_arm_lifts_what_it_can_and_deposits_what_it_cannot() {
        // The third arm the write-back dilemma omitted: apply the lift where it
        // is defined, gate on the boolean, deposit the refused hinges as a
        // population. Measured, not asserted.
        let (standing, [first, second]) = octahedron_with_two_orthogonal_responses();
        let before = read(&standing).expect("the reading succeeds");
        assert!(
            step(&standing).is_err(),
            "the whole arm refuses this standing, so the two arms differ here"
        );

        let mut moved = standing.clone();
        let applied = revise_partially(&mut moved).expect("the partial arm conducts");
        assert!(!applied.is_whole());
        assert_eq!(
            applied.unlifted.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([first, second])
        );
        assert_eq!(applied.revisions.len(), 10);
        assert!(applied.flow.moved);

        // The deposit is complete: ten hinges moved, two are verbatim.
        for hinge in standing.geometry_responses.keys() {
            if applied.unlifted.contains_key(hinge) {
                assert_eq!(moved.geometry_responses[hinge], standing.geometry_responses[hinge]);
            } else {
                assert_ne!(moved.geometry_responses[hinge], standing.geometry_responses[hinge]);
            }
        }
        // It is NOT a no-op: the deficit population actually moved.
        let after = read(&moved).expect("the moved standing conducts");
        assert_ne!(after.deficits(), before.deficits());

        // And the exact price of the arm, which is the reason the population
        // must be deposited: the successor differs from the carrier's own
        // successor by exactly the retained increment at the four endpoints of
        // the two unlifted hinges, and by exactly nothing anywhere else.
        let mut owed: BTreeMap<VertexId, Rat> = BTreeMap::new();
        for (hinge, refused) in &applied.unlifted {
            let increment = &applied.flow.revisions[hinge];
            for endpoint in [refused.edge.lower, refused.edge.upper] {
                *owed.entry(endpoint).or_insert_with(Rat::zero) += increment;
            }
        }
        assert_eq!(owed.len(), 4);
        for (vertex, expected) in &applied.flow.deficits_after {
            let owed_here = owed.get(vertex).cloned().unwrap_or_else(Rat::zero);
            assert_eq!(
                after.deficits()[vertex],
                expected + &owed_here,
                "vertex {vertex:?} must differ from the carrier's successor by \
                 exactly the increment the unlifted hinges never received"
            );
        }
        assert!(
            owed.values().any(|value| !value.is_zero()),
            "a discrepancy of zero everywhere would make the assertion above \
             vacuous"
        );
    }

    #[test]
    fn a_zero_successor_scalar_collapses_the_response_and_the_next_step_refuses() {
        // A hinge whose successor scalar is exactly zero is admitted: the
        // factor is zero and the response collapses onto the origin of its own
        // line. That terminus is reached by the law, not chosen by the bridge,
        // and the following step refuses it.
        let projection = HingeResponseProjection {
            hinge: HingeId(1),
            edge: Edge::new(VertexId(1), VertexId(2)).unwrap(),
            response_direction: RatVec3::from_i64(2, 4, 6),
            edge_vector: RatVec3::from_i64(1, 0, 0),
            along_edge: integer(2),
            direction_blind_norm_squared: integer(56),
        };
        let collapsed = lift_along_edge(&projection, Rat::zero()).expect("zero is reachable");
        assert_eq!(collapsed.magnitude_factor, Rat::zero());
        assert_eq!(collapsed.after, RatVec3::zero());
        assert_eq!(collapsed.after.dot(&projection.edge_vector), Rat::zero());

        let next = HingeResponseProjection {
            response_direction: collapsed.after.clone(),
            along_edge: collapsed.after.dot(&projection.edge_vector),
            direction_blind_norm_squared: collapsed.after.norm_squared(),
            ..projection.clone()
        };
        assert_eq!(
            lift_along_edge(&next, integer(1)),
            Err(OrthogonalHinge {
                hinge: HingeId(1),
                edge: projection.edge,
                response_direction: RatVec3::zero(),
                edge_vector: RatVec3::from_i64(1, 0, 0),
                requested: integer(1),
            })
        );

        // A nonzero request from a nonzero projection is reachable, so the
        // refusal above is not the only outcome this lift can return.
        let revived = lift_along_edge(&projection, integer(-3)).expect("a sign change is a lift");
        assert_eq!(revived.magnitude_factor, rat(-3, 2));
        assert_eq!(
            revived.after,
            RatVec3::new(integer(-3), integer(-6), integer(-9))
        );
        assert_eq!(revived.after.dot(&projection.edge_vector), integer(-3));
        assert_eq!(revived.after.cross(&revived.before), RatVec3::zero());
    }

    // ---------------------------------------------------------------
    // The bridge is exact, and one route is checked against another.
    // ---------------------------------------------------------------

    #[test]
    fn the_successor_deficits_recomputed_from_the_deposited_responses_agree_with_the_carriers() {
        // The genuinely independent frame. `read` is not called: the successor
        // deficit is rebuilt from the DEPOSITED `RatVec3` population, the
        // complex's own hinge edges and the spatial standing's own edge
        // vectors, by the definition `K(v) = 6 - sum of incident projections`.
        // A wrong projection, a wrong write-back or a wrong edge lookup all
        // surface here, and none of them is a field identity.
        let (standing, _, _) = bipyramid(|edge, apexes| {
            if touches_apex(edge, apexes) {
                rat(7, 3)
            } else {
                rat(-2, 5)
            }
        });
        let applied = step(&standing).expect("the bipyramid conducts");
        let complex = &standing.kinematic.complex;

        let mut recomputed = applied
            .before
            .aperture
            .conducted
            .keys()
            .map(|vertex| (*vertex, integer(FLAT_COORDINATION)))
            .collect::<BTreeMap<VertexId, Rat>>();
        for hinge in &applied.before.aperture.conducted_hinges {
            let edge = complex.hinges[hinge].edge;
            let spent = applied.revised_geometry_responses[hinge]
                .dot(&standing.spatial.edges[&edge].vector);
            for endpoint in [edge.lower, edge.upper] {
                *recomputed
                    .get_mut(&endpoint)
                    .expect("a conducted hinge has conducted endpoints") -= &spent;
            }
        }
        assert_eq!(recomputed, applied.flow.deficits_after);
        assert!(
            recomputed.values().cloned().collect::<BTreeSet<_>>().len() >= 2,
            "the successor deficits must vary, or agreement proves nothing"
        );
    }

    #[test]
    fn the_carrier_reached_through_the_bridge_agrees_with_its_own_closed_form() {
        // ONE numeric route, stated as such. The lift sets
        // `after = before.scale(along_edge_after / along_edge_before)`, so
        // `after . edge == along_edge_after` is an exact field identity and
        // re-reading the revised standing cannot return anything but the
        // carrier's own stepped responses. What this test therefore establishes
        // is NOT an independent numeric check — see the test above for that —
        // but that the write-back actually reached the standing, and that the
        // carrier's closed form `K'(v) = -sum of far-endpoint traced
        // deviations` survives the round trip through `RatVec3`.
        let (mut standing, _, _) = bipyramid(|edge, apexes| {
            if touches_apex(edge, apexes) {
                rat(7, 3)
            } else {
                rat(-2, 5)
            }
        });
        for _ in 0..4 {
            let reading = read(&standing).expect("the bipyramid conducts");
            let predicted = reading.configuration.predicted_deficits();
            let applied = revise(&mut standing).expect("the bipyramid conducts");
            assert!(applied.flow.moved);
            let observed = read(&standing).expect("the bipyramid conducts").deficits();
            assert_eq!(
                predicted, observed,
                "the closed form and the round trip through RatVec3 must agree"
            );
            let distinct = observed.into_values().collect::<BTreeSet<_>>();
            assert!(
                distinct.len() >= 2,
                "the successor deficits must vary, or agreement proves nothing"
            );
        }
    }

    #[test]
    fn the_hinge_population_the_bridge_hands_over_is_the_aperture_population() {
        let standing = octahedron(|_| rat(5, 4));
        let reading = read(&standing).expect("the octahedron conducts");
        let carried = reading
            .configuration
            .hinges()
            .map(|hinge: &CurvatureHinge| hinge.id)
            .collect::<BTreeSet<_>>();
        assert_eq!(carried, reading.aperture.conducted_hinges);
        for hinge in reading.configuration.hinges() {
            let edge = standing.kinematic.complex.hinges[&hinge.id].edge;
            assert_eq!(hinge.endpoints, [edge.lower, edge.upper]);
            assert_eq!(hinge.response, reading.projections[&hinge.id].along_edge);
        }
    }

    #[test]
    fn every_deposit_names_the_schema_a_later_reader_will_key_on() {
        let standing = octahedron(|_| integer(1));
        let reading = read(&standing).expect("the octahedron conducts");
        assert_eq!(
            reading.schema,
            "holonic-engine.curvature-bridge-reading.v1"
        );
        assert_eq!(
            reading.aperture.schema,
            "holonic-engine.curvature-bridge-aperture.v1"
        );

        let applied = step(&standing).expect("the octahedron conducts");
        assert_eq!(applied.schema, "holonic-engine.curvature-bridge-step.v1");
        assert_eq!(
            applied.before.schema,
            "holonic-engine.curvature-bridge-reading.v1"
        );

        let partial = step_partially(&standing).expect("the octahedron conducts");
        assert_eq!(
            partial.schema,
            "holonic-engine.curvature-bridge-partial-step.v1"
        );
        // The four names are distinct, so a reader keying on one cannot be
        // handed another.
        assert_eq!(
            BTreeSet::from([
                reading.schema.as_str(),
                reading.aperture.schema.as_str(),
                applied.schema.as_str(),
                partial.schema.as_str(),
            ])
            .len(),
            4
        );
    }
}
