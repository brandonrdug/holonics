//! The closed discrete-curvature loop: deficit returned, response revised.
//!
//! # What this module closes
//!
//! `local_star.rs` already *computes* the discrete disclination charge.
//! `coordination_defect` (`local_star.rs:1143`) derives, from the actual
//! simplicial link of a vertex, the codimension-two Regge hinge curvature
//!
//! ```text
//! charge(v) = 6 - |link(v)|
//! ```
//!
//! and `LocalStarStanding::coordination_defects` (`local_star.rs:791`)
//! publishes it for every vertex. The layout then **discards it**. The
//! constitutive directions live in `LocalStarStanding::geometry_responses`
//! (`local_star.rs:772`); they are read at `local_star.rs:2082` to scale a
//! coordinate change into a vertex displacement, and the successor standing
//! clones them verbatim at `local_star.rs:2301`. Nothing the layout returned
//! — least of all the curvature it just measured — ever revises a response.
//! The response population is supplied once by the caller and is thereafter a
//! constant of the motion.
//!
//! This module closes that loop on its own exact carrier. It does not mutate
//! `local_star`; it owns a bare hinge incidence with one exact rational datum
//! per hinge, defines the deficit on it, and states the law by which a
//! returned deficit revises the responses that produced it.
//!
//! # What this flow is, named 2026-08-10
//!
//! Feeding a returned deficit back into the metric that produced it is
//! **Chow–Luo's combinatorial Ricci flow** by construction, and the ratified
//! reading of what that means is
//! `research/records/2026-07-19_THE_RICCI_TRACE_CHANGES_THE_RECEIVER_THE_SINGULAR_NECK_REBASES_THE_BODY.md`:
//!
//! > *"For a declared Riemannian receiver, Ricci curvature is, up to the
//! > record's curvature-sign convention, the transverse trace of gravitas.
//! > Ricci flow feeds that receiver quotient back into the metric by which
//! > later continuations are compared."*
//!
//! **And the law below is not a flow.** It satisfies
//! `Σ_v K'(v) = −Σ_v K(v)` — an exact *involution* on the total-curvature
//! functional, which alternates rather than converging. Ricci flow's whole
//! content is dissipative approach to a constant-curvature metric, and an
//! involution cannot perform it. The `c = 1` derived below is unique for
//! annulling a vertex's own deficit, and that is precisely the coefficient
//! that makes the total map a reflection instead of a contraction.
//!
//! So this organ is a curvature **feedback** with the Ricci shape and a
//! **reflective** law.
//!
//! **The convergent coefficient is solved, 2026-08-10.** [`total_multiplier`]
//! proves `Sigma K' = (1 - 2c) Sigma K` in two lines, so `c = 1` is exactly
//! the multiplier `-1` — a reflection — and `c = 1/2` is the unique
//! annihilator. `c = 1/2` against `c = 1` is `I - P` against `I - 2P`: the
//! projection and the reflection it doubles, which is `CLAUDE.md` §2b's half
//! turn arriving from the curvature side. [`step_at`] takes the coefficient
//! from the caller and [`coefficient_species`] says exactly what it does.
//!
//! Two bounds travel with it. The total and the pointwise amplitude are
//! independent, and on a **bipartite** incidence the alternating deficit is an
//! eigenvector with eigenvalue `1` at every coefficient — two-colourability is
//! the obstruction to convergence, which is this module's own
//! [`CurvatureFixedPoint::AlternatingTracedDeviation`]. And on a `d`-regular
//! component at unit response `c = 1/2` flattens in one step *by arithmetic*,
//! which is a property of the incidence and not of the coefficient.
//!
//! `docs/canon/TABLET_THE_TURN.md` §11.6 carries the statement and both bounds.
//!
//! # The carrier
//!
//! A [`DiscreteCurvatureConfiguration`] is a finite hinge incidence:
//!
//! - a population of vertices, each declaring a **link size** `n_v`, certified
//!   at construction against the vertex's actual incident-hinge count;
//! - a population of hinges, each joining two distinct vertices and carrying
//!   one exact **response** `r_e in Rat` — the hinge's metric datum, the
//!   scalar content of the `RatVec3` that `geometry_responses` carries.
//!
//! Everything below is exact rational arithmetic. There is no float, no
//! tolerance, no threshold, no rate, and no fitted constant anywhere in this
//! file.
//!
//! # The law
//!
//! One declared constant, [`FLAT_COORDINATION`] `= 6`, the hexagonal
//! reference coordination. It is not chosen here: it is transcribed from
//! `local_star.rs:1151`, where the charge is `6 - |link|`.
//!
//! **Definition (deficit).** For a vertex `v`,
//!
//! ```text
//! K(v) = FLAT_COORDINATION - sum over hinges e incident to v of r_e
//! ```
//!
//! At **unit response** (`r_e = 1` for every hinge) this is exactly
//! `6 - n_v`, the charge computed at `local_star.rs:1151`. The deficit is the
//! metric refinement of that combinatorial charge: the combinatorics fixes
//! how many hinges report, the responses fix what each one reports.
//!
//! **Definition (traced deviation).** For a vertex `v`,
//!
//! ```text
//! h(v) = K(v) / n_v
//! ```
//!
//! the vertex's whole deficit traced over its own hinge population — its
//! exact per-hinge share.
//!
//! **THE UPDATE LAW.** For every hinge `e = {u, v}`, simultaneously,
//!
//! ```text
//! r_e  <-  r_e + h(u) + h(v)
//! ```
//!
//! In words: *every vertex discharges its entire deficit into its own hinges
//! in equal exact shares, and every hinge accepts the share of each of its two
//! endpoints.*
//!
//! **The law introduces no scale.** The only scale that appears is `1/n_v`,
//! and that is the vertex's own declared link size, read off the carrier. The
//! coefficient on the discharge is `1` and is *derived, not chosen*: for
//! `r_e <- r_e + c(h(u) + h(v))` the successor deficit is
//! `K'(v) = (1 - c) K(v) - c * sum over neighbours of h(w)`, and `c = 1` is
//! the unique value at which a vertex's own discharge exactly annuls its own
//! deficit. Any other `c` leaves the vertex partly paying for curvature it has
//! already discharged.
//!
//! # Consequence 1: the successor deficit in closed form
//!
//! ```text
//! K'(v) = - sum over hinges e incident to v of h(w_e)
//! ```
//!
//! where `w_e` is the far endpoint of `e` from `v`.
//!
//! *Proof.* `K'(v) = F - sum_e (r_e + h(v) + h(w_e))
//! = K(v) - n_v h(v) - sum_e h(w_e) = -sum_e h(w_e)`, since `n_v h(v) = K(v)`.
//!
//! So a vertex's own curvature is annulled exactly by its own discharge, and
//! what returns to it is *only* its neighbours' shares, sign-reversed.
//! **Curvature is transported onto the link and inverted; it is never
//! dissipated and never absorbed.** [`DiscreteCurvatureConfiguration::
//! predicted_deficits`] evaluates this closed form directly, by a code path
//! that never touches a response, and is therefore an independent check on
//! the response update.
//!
//! # Consequence 2: total curvature is NEGATED, not preserved
//!
//! This must be said plainly, because the discrete Gauss-Bonnet total is a
//! topological invariant of the incidence and one might expect a curvature
//! flow to preserve it. **This law does not.**
//!
//! ```text
//! sum over v of K'(v) = - sum over v of K(v)
//! ```
//!
//! *Proof.* `sum_v K'(v) = -sum_v sum_{e incident v} h(w_e)
//! = -sum_e (h(u_e) + h(v_e)) = -sum_v n_v h(v) = -sum_v K(v)`, using that
//! every hinge contributes exactly two endpoint incidences.
//!
//! What is preserved, exactly and at every step, is therefore:
//!
//! - the **magnitude** `|sum_v K(v)|`;
//! - the total under the **doubled** flow: `sum_v K''(v) = sum_v K(v)`, so the
//!   flow is an exact involution on the total-curvature functional;
//! - consequently the discrete Gauss-Bonnet value itself, `sum_v K(v) = 6 chi`
//!   at unit response on a closed triangulated surface, is preserved outright
//!   exactly when `chi = 0`, and otherwise alternates in sign with its
//!   magnitude standing.
//!
//! No contraction is claimed. The iterates of a charged configuration do not
//! in general shrink; this is a signed transport law, not a smoothing.
//!
//! # Consequence 3: the fixed points, completely
//!
//! The flow leaves a configuration alone exactly when every revision
//! vanishes, that is when
//!
//! ```text
//! h(u) + h(v) = 0   for every hinge {u, v}.
//! ```
//!
//! So the traced deviation must alternate in sign along every hinge. Per
//! connected component `C` of the hinge incidence:
//!
//! 1. **`C` carries an odd hinge cycle.** Alternation around an odd cycle is
//!    inconsistent, so `h == 0` on `C`, hence `K == 0` on `C`. **Flat is the
//!    only fixed configuration on such a component.**
//! 2. **`C` is bipartite**, with parts `A` (the part containing `C`'s least
//!    vertex) and `B`. Then `h == t_C` on `A` and `h == -t_C` on `B`, i.e.
//!    `K(v) = ±t_C * n_v`. The scale `t_C` is **not free**. For any
//!    configuration whatever, summing the deficit over each part gives
//!    `sum_A K - sum_B K = F * (|A| - |B|)`, because each hinge of a bipartite
//!    component contributes its response to exactly one vertex of each part.
//!    At a fixed point the left side is `2 t_C |E_C|`, so
//!
//!    ```text
//!    t_C = FLAT_COORDINATION * (|A_C| - |B_C|) / (2 |E_C|)
//!    ```
//!
//!    [`DiscreteCurvatureConfiguration::forced_component_scale`] computes this
//!    from the bipartition alone — pure counting, no response is read.
//!
//! Two corollaries worth stating, because they are what make the
//! characterization sharp rather than decorative:
//!
//! - A **balanced** bipartite component (`|A| = |B|`) forces `t_C = 0`, so
//!   there too flat is the only fixed configuration. An even cycle is fixed
//!   only when flat, exactly like an odd cycle, and for a different reason.
//! - A bipartite component with `|A| != |B|` admits a **nonflat** fixed
//!   configuration, and it exists: on a connected bipartite graph the left
//!   kernel of the unsigned incidence matrix is spanned by `chi_A - chi_B`, so
//!   the single condition above is not merely necessary but sufficient for the
//!   required deficit to be realized by some response population.
//!
//! # Relation to the archived Regge reading
//!
//! `K(v)` here is Regge's deficit at a codimension-two hinge, in the units in
//! which an equilateral corner angle is `1/3` of a half-turn: the piecewise-flat
//! deficit `2 - sum of corner angles` (in half-turns) is `(6 - n_v)/3`, so
//! `6 - n_v` is exactly three times the Regge deficit and is an integer. This
//! module keeps the integer normalization of `local_star.rs:1151` so that the
//! bridge to that site is an equality and not a conversion.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{HingeId, VertexId};

/// The hexagonal reference coordination, transcribed from the charge
/// expression at `local_star.rs:1151`.
///
/// This is the module's only declared constant. It is a reference, not a
/// tuning: at unit response it makes [`DiscreteCurvatureConfiguration::deficit`]
/// equal `6 - |link|` on the nose.
pub const FLAT_COORDINATION: i64 = 6;

fn flat_coordination() -> Rat {
    Rat::from_integer(BigInt::from(FLAT_COORDINATION))
}

fn count(value: usize) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

// -------------------------------------------------------------------------------------------------
// The discharge coefficient, and the exact law it obeys on the total
// -------------------------------------------------------------------------------------------------

/// **`Sigma K' = (1 - 2c) Sigma K`**, exactly, for any discharge coefficient `c`.
///
/// # The two-line proof
///
/// Let `B` be the unsigned vertex-hinge incidence, `D = diag(n_v)`, `A` the vertex adjacency. Then
/// `K = F*1 - B r` and `h = D^-1 K`, and the law `r <- r + c B^T h` gives
///
/// ```text
/// K' = F*1 - B r' = K - c B B^T D^-1 K = K - c (D + A) D^-1 K
/// ```
///
/// because `B B^T = D + A` — the diagonal counts a vertex's own hinges and the off-diagonal counts
/// the one hinge joining two vertices. Summing, `1^T (D + A) = (n_v)^T + (n_v)^T = 2 (n_v)^T`, so
/// `1^T (D + A) D^-1 = 2 * 1^T` and
///
/// ```text
/// Sigma K' = 1^T K - 2c * 1^T K = (1 - 2c) Sigma K.
/// ```
///
/// # What that settles
///
/// The module's derived `c = 1` — the unique coefficient at which a vertex's own discharge annuls
/// its own deficit — is exactly the coefficient at which this multiplier is `-1`. **The law is a
/// reflection on the total-curvature functional, and a reflection does not converge.**
///
/// `research/records/2026-07-19_THE_RICCI_TRACE_CHANGES_THE_RECEIVER_THE_SINGULAR_NECK_REBASES_THE_BODY.md`
/// is ratified that *"Ricci flow feeds that receiver quotient back into the metric by which later
/// continuations are compared"*, and the content of a flow is dissipative approach. So the
/// multiplier is the discriminant, and it is `1 - 2c`:
///
/// ```text
/// c = 0        multiplier  1     inert
/// 0 < c < 1/2  in (0, 1)         dissipative
/// c = 1/2      multiplier  0     ANNIHILATING — the total is zero after one step
/// 1/2 < c < 1  in (-1, 0)        dissipative, overshooting
/// c = 1        multiplier -1     REFLECTIVE — the module's derived law
/// otherwise    |multiplier| > 1  expanding
/// ```
///
/// **`c = 1/2` against `c = 1` is `I - P` against `I - 2P`** — the projection and the reflection it
/// doubles. `CLAUDE.md` §2b: the involution is a half turn on a magnitude, and the projection is the
/// half of it. The live law overshoots the dissipative one by exactly a factor of two.
pub fn total_multiplier(coefficient: &Rat) -> Rat {
    Rat::from_integer(BigInt::from(1)) - Rat::from_integer(BigInt::from(2)) * coefficient
}

/// **The unique coefficient that annihilates the total curvature in one step**, `c = 1/2`.
///
/// Derived, not chosen: it is the one root of `1 - 2c = 0`. Nothing is authored — the value is a
/// theorem about [`total_multiplier`], and the module's own `c = 1` is the other distinguished root
/// of `|1 - 2c| = 1`.
pub fn dissipative_annihilator() -> Rat {
    Rat::new(BigInt::from(1), BigInt::from(2))
}

/// What a declared discharge coefficient does to the total-curvature functional, read off
/// [`total_multiplier`] exactly and never from a tolerance.
///
/// This **classifies and does not refuse**. The coefficient is the caller's declaration; the species
/// is derived from it. `CLAUDE.md` §13 rule 2 — count freely, report what you count, never let a
/// count quietly decide.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoefficientSpecies {
    /// `c = 0`. Multiplier `1`. Nothing is discharged and nothing moves.
    Inert,
    /// `0 < |1 - 2c| < 1`. The total contracts geometrically. This is the flow.
    Dissipative,
    /// `c = 1/2`. Multiplier `0`. The total is exactly zero after one step.
    Annihilating,
    /// `c = 1`. Multiplier `-1`. An involution: the total alternates and never decays.
    Reflective,
    /// `|1 - 2c| > 1`. The total grows.
    Expanding,
}

/// Classify a declared coefficient by its exact multiplier.
pub fn coefficient_species(coefficient: &Rat) -> CoefficientSpecies {
    let one = Rat::from_integer(BigInt::from(1));
    let multiplier = total_multiplier(coefficient);
    if coefficient.is_zero() {
        return CoefficientSpecies::Inert;
    }
    if multiplier.is_zero() {
        return CoefficientSpecies::Annihilating;
    }
    if multiplier == -one.clone() {
        return CoefficientSpecies::Reflective;
    }
    let magnitude = if multiplier < Rat::zero() {
        -multiplier
    } else {
        multiplier
    };
    if magnitude < one {
        CoefficientSpecies::Dissipative
    } else {
        CoefficientSpecies::Expanding
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum DiscreteCurvatureError {
    #[error("hinge {0:?} was declared twice")]
    DuplicateHinge(HingeId),
    #[error("vertex {0:?} was declared twice")]
    DuplicateVertex(VertexId),
    #[error("hinge {hinge:?} names vertex {vertex:?}, which the configuration does not carry")]
    UnknownHingeEndpoint { hinge: HingeId, vertex: VertexId },
    #[error("vertex {0:?} is not carried by this configuration")]
    UnknownVertex(VertexId),
    #[error("hinge {0:?} is not carried by this configuration")]
    UnknownHinge(HingeId),
    /// A hinge joining a vertex to itself has no far endpoint, so the law's
    /// two-endpoint discharge and the two-incidence counting that proves
    /// Consequence 2 both fail. It is refused rather than silently reinterpreted.
    #[error("hinge {hinge:?} joins vertex {vertex:?} to itself")]
    SelfIncidentHinge { hinge: HingeId, vertex: VertexId },
    /// An isolated vertex has `n_v = 0`, so its traced deviation is undefined
    /// and its deficit can never be discharged. Isolated links are a typed
    /// structural fact in `local_star` as well
    /// (`LocalCoordinationDefect::Isolated`) and carry no doctrine here either.
    #[error("vertex {0:?} is incident to no hinge, so its traced deviation is undefined")]
    IsolatedVertex(VertexId),
    #[error("vertex {vertex:?} declares link size {declared} but is incident to {incident} hinges")]
    DeclaredLinkSizeDisagreesWithIncidence {
        vertex: VertexId,
        declared: usize,
        incident: usize,
    },
}

/// One hinge of the curvature carrier: an unordered pair of distinct vertices
/// and one exact metric response.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurvatureHinge {
    pub id: HingeId,
    /// Stored in ascending vertex order so the carrier is canonical.
    pub endpoints: [VertexId; 2],
    /// The hinge's exact metric datum. At `1` the hinge reports exactly one
    /// unit of coordination and the deficit reduces to `6 - |link|`.
    pub response: Rat,
}

impl CurvatureHinge {
    /// The endpoint of this hinge other than `vertex`.
    pub fn far_endpoint(&self, vertex: VertexId) -> Option<VertexId> {
        if self.endpoints[0] == vertex {
            Some(self.endpoints[1])
        } else if self.endpoints[1] == vertex {
            Some(self.endpoints[0])
        } else {
            None
        }
    }
}

/// The parity structure of the hinge incidence, which is what decides the
/// fixed-point classification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IncidenceParity {
    /// Component key per vertex: the least vertex of that vertex's component.
    pub component: BTreeMap<VertexId, VertexId>,
    /// Two-colouring, `true` on the part containing the component's least
    /// vertex. A vertex in a component carrying an odd hinge cycle is absent.
    pub parity: BTreeMap<VertexId, bool>,
    /// Components carrying an odd hinge cycle, keyed by least vertex.
    pub odd_cycle_components: BTreeSet<VertexId>,
}

impl IncidenceParity {
    pub fn carries_odd_hinge_cycle(&self) -> bool {
        !self.odd_cycle_components.is_empty()
    }
}

/// The complete record of one application of the update law.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurvatureFlowStep {
    pub deficits_before: BTreeMap<VertexId, Rat>,
    pub traced_deviations: BTreeMap<VertexId, Rat>,
    /// The exact increment applied to each hinge response.
    pub revisions: BTreeMap<HingeId, Rat>,
    pub deficits_after: BTreeMap<VertexId, Rat>,
    pub total_deficit_before: Rat,
    pub total_deficit_after: Rat,
    /// True when at least one revision was nonzero.
    pub moved: bool,
}

/// Which fixed class a configuration falls in, per the characterization in the
/// module documentation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CurvatureFixedPoint {
    /// Every deficit is exactly zero. Fixed on any incidence whatever.
    Flat,
    /// Fixed with at least one nonzero deficit. Occurs only on bipartite
    /// components with unequal parts; the observed scale `t_C` is carried per
    /// component, keyed by that component's least vertex.
    AlternatingTracedDeviation {
        component_scale: BTreeMap<VertexId, Rat>,
    },
    /// Not fixed. Carries every hinge whose revision is nonzero.
    Moving { revisions: BTreeMap<HingeId, Rat> },
}

/// A hinge incidence carrying one exact response per hinge and one certified
/// link size per vertex.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiscreteCurvatureConfiguration {
    pub schema: String,
    /// Declared link size per vertex, certified equal to incident hinge count.
    link_sizes: BTreeMap<VertexId, usize>,
    hinges: BTreeMap<HingeId, CurvatureHinge>,
    /// Derived incidence: every hinge touching a vertex, with multiplicity, so
    /// parallel hinges each report.
    incidence: BTreeMap<VertexId, Vec<HingeId>>,
}

impl DiscreteCurvatureConfiguration {
    /// Found a configuration from declared vertices and declared hinges.
    ///
    /// Refuses a self-incident hinge, an isolated vertex, an unknown endpoint,
    /// a duplicate declaration, and — the load-bearing check — any vertex
    /// whose declared link size disagrees with its actual hinge incidence.
    /// That agreement is what makes Consequence 2's counting exact.
    pub fn found(
        vertices: impl IntoIterator<Item = (VertexId, usize)>,
        hinges: impl IntoIterator<Item = (HingeId, [VertexId; 2], Rat)>,
    ) -> Result<Self, DiscreteCurvatureError> {
        let mut link_sizes = BTreeMap::new();
        for (vertex, link_size) in vertices {
            if link_sizes.insert(vertex, link_size).is_some() {
                return Err(DiscreteCurvatureError::DuplicateVertex(vertex));
            }
        }
        let mut carried = BTreeMap::new();
        let mut incidence: BTreeMap<VertexId, Vec<HingeId>> = link_sizes
            .keys()
            .copied()
            .map(|vertex| (vertex, Vec::new()))
            .collect();
        for (id, endpoints, response) in hinges {
            if endpoints[0] == endpoints[1] {
                return Err(DiscreteCurvatureError::SelfIncidentHinge {
                    hinge: id,
                    vertex: endpoints[0],
                });
            }
            for vertex in endpoints {
                if !link_sizes.contains_key(&vertex) {
                    return Err(DiscreteCurvatureError::UnknownHingeEndpoint { hinge: id, vertex });
                }
            }
            let mut endpoints = endpoints;
            endpoints.sort();
            if carried
                .insert(
                    id,
                    CurvatureHinge {
                        id,
                        endpoints,
                        response,
                    },
                )
                .is_some()
            {
                return Err(DiscreteCurvatureError::DuplicateHinge(id));
            }
            for vertex in endpoints {
                incidence
                    .get_mut(&vertex)
                    .expect("the endpoint was checked against the vertex population")
                    .push(id);
            }
        }
        for (vertex, declared) in &link_sizes {
            let incident = incidence[vertex].len();
            if incident == 0 {
                return Err(DiscreteCurvatureError::IsolatedVertex(*vertex));
            }
            if *declared != incident {
                return Err(
                    DiscreteCurvatureError::DeclaredLinkSizeDisagreesWithIncidence {
                        vertex: *vertex,
                        declared: *declared,
                        incident,
                    },
                );
            }
        }
        Ok(Self {
            schema: "holonic-engine.discrete-curvature-configuration.v1".to_owned(),
            link_sizes,
            hinges: carried,
            incidence,
        })
    }

    /// Found a configuration in which every hinge carries unit response, with
    /// link sizes derived from the declared incidence.
    ///
    /// This is the configuration on which [`Self::deficit`] reproduces
    /// `local_star`'s `6 - |link|` exactly.
    pub fn at_unit_response(
        hinges: impl IntoIterator<Item = (HingeId, [VertexId; 2])>,
    ) -> Result<Self, DiscreteCurvatureError> {
        let hinges = hinges.into_iter().collect::<Vec<_>>();
        let mut degrees: BTreeMap<VertexId, usize> = BTreeMap::new();
        for (_, endpoints) in &hinges {
            for vertex in endpoints {
                *degrees.entry(*vertex).or_insert(0) += 1;
            }
        }
        let unit = Rat::from_integer(BigInt::from(1));
        Self::found(
            degrees,
            hinges
                .into_iter()
                .map(|(id, endpoints)| (id, endpoints, unit.clone())),
        )
    }

    pub fn vertices(&self) -> impl Iterator<Item = VertexId> + '_ {
        self.link_sizes.keys().copied()
    }

    pub fn hinges(&self) -> impl Iterator<Item = &CurvatureHinge> {
        self.hinges.values()
    }

    pub fn link_size(&self, vertex: VertexId) -> Result<usize, DiscreteCurvatureError> {
        self.link_sizes
            .get(&vertex)
            .copied()
            .ok_or(DiscreteCurvatureError::UnknownVertex(vertex))
    }

    pub fn response(&self, hinge: HingeId) -> Result<&Rat, DiscreteCurvatureError> {
        self.hinges
            .get(&hinge)
            .map(|carried| &carried.response)
            .ok_or(DiscreteCurvatureError::UnknownHinge(hinge))
    }

    pub fn responses(&self) -> BTreeMap<HingeId, Rat> {
        self.hinges
            .iter()
            .map(|(id, carried)| (*id, carried.response.clone()))
            .collect()
    }

    /// The purely combinatorial charge `6 - n_v` of `local_star.rs:1151`.
    ///
    /// This is what [`Self::deficit`] returns at unit response, and is carried
    /// separately so the bridge can be checked rather than asserted.
    pub fn combinatorial_charge(&self, vertex: VertexId) -> Result<i64, DiscreteCurvatureError> {
        let link_size = self.link_size(vertex)?;
        Ok(FLAT_COORDINATION
            - i64::try_from(link_size).expect("a finite local link cardinality fits i64"))
    }

    /// `K(v) = FLAT_COORDINATION - sum of incident responses`. Exact.
    pub fn deficit(&self, vertex: VertexId) -> Result<Rat, DiscreteCurvatureError> {
        let incident = self
            .incidence
            .get(&vertex)
            .ok_or(DiscreteCurvatureError::UnknownVertex(vertex))?;
        let mut reported = Rat::zero();
        for hinge in incident {
            reported += &self.hinges[hinge].response;
        }
        Ok(flat_coordination() - reported)
    }

    pub fn deficits(&self) -> BTreeMap<VertexId, Rat> {
        self.vertices()
            .map(|vertex| {
                let deficit = self
                    .deficit(vertex)
                    .expect("a carried vertex has a deficit");
                (vertex, deficit)
            })
            .collect()
    }

    /// `sum over v of K(v)`. At unit response on a closed triangulated surface
    /// this is the discrete Gauss-Bonnet total `6 chi`.
    pub fn total_deficit(&self) -> Rat {
        self.deficits()
            .values()
            .fold(Rat::zero(), |sum, deficit| sum + deficit)
    }

    pub fn is_flat(&self) -> bool {
        self.deficits().values().all(Rat::is_zero)
    }

    /// `h(v) = K(v) / n_v`: the vertex's deficit traced over its own hinges.
    pub fn traced_deviation(&self, vertex: VertexId) -> Result<Rat, DiscreteCurvatureError> {
        let deficit = self.deficit(vertex)?;
        let link_size = self.link_size(vertex)?;
        Ok(deficit / count(link_size))
    }

    pub fn traced_deviations(&self) -> BTreeMap<VertexId, Rat> {
        self.vertices()
            .map(|vertex| {
                let deviation = self
                    .traced_deviation(vertex)
                    .expect("a carried vertex has a traced deviation");
                (vertex, deviation)
            })
            .collect()
    }

    /// The exact increment the law applies to one hinge: `h(u) + h(v)`.
    pub fn hinge_revision(&self, hinge: HingeId) -> Result<Rat, DiscreteCurvatureError> {
        let carried = self
            .hinges
            .get(&hinge)
            .ok_or(DiscreteCurvatureError::UnknownHinge(hinge))?;
        Ok(self.traced_deviation(carried.endpoints[0])?
            + self.traced_deviation(carried.endpoints[1])?)
    }

    pub fn revisions(&self) -> BTreeMap<HingeId, Rat> {
        let deviations = self.traced_deviations();
        self.hinges
            .iter()
            .map(|(id, carried)| {
                (
                    *id,
                    &deviations[&carried.endpoints[0]] + &deviations[&carried.endpoints[1]],
                )
            })
            .collect()
    }

    /// The successor deficits by the closed form of Consequence 1,
    /// `K'(v) = -sum over incident hinges of h(far endpoint)`.
    ///
    /// This route never reads or writes a response. It exists as an
    /// independent check on [`Self::step`], which reaches the same values by
    /// revising responses and recomputing.
    pub fn predicted_deficits(&self) -> BTreeMap<VertexId, Rat> {
        let deviations = self.traced_deviations();
        self.vertices()
            .map(|vertex| {
                let mut carried = Rat::zero();
                for hinge in &self.incidence[&vertex] {
                    let far = self.hinges[hinge]
                        .far_endpoint(vertex)
                        .expect("an incident hinge names this vertex");
                    carried += &deviations[&far];
                }
                (vertex, -carried)
            })
            .collect()
    }

    /// The increment the law applies to one hinge under a **declared** discharge coefficient:
    /// `c * (h(u) + h(v))`.
    pub fn hinge_revision_at(
        &self,
        hinge: HingeId,
        coefficient: &Rat,
    ) -> Result<Rat, DiscreteCurvatureError> {
        Ok(coefficient * self.hinge_revision(hinge)?)
    }

    /// [`Self::revisions`] under a declared discharge coefficient.
    pub fn revisions_at(&self, coefficient: &Rat) -> BTreeMap<HingeId, Rat> {
        self.revisions()
            .into_iter()
            .map(|(id, revision)| (id, coefficient * revision))
            .collect()
    }

    /// The successor deficits in closed form under a declared coefficient,
    /// `K'(v) = (1 - c) K(v) - c * sum over neighbours of h(w)`.
    ///
    /// Like [`Self::predicted_deficits`] this route never reads or writes a response, so it is an
    /// independent check on [`Self::step_at`]. At `c = 1` it reduces to the closed form the module
    /// header proves.
    pub fn predicted_deficits_at(&self, coefficient: &Rat) -> BTreeMap<VertexId, Rat> {
        let one = Rat::from_integer(BigInt::from(1));
        let deviations = self.traced_deviations();
        let deficits = self.deficits();
        self.vertices()
            .map(|vertex| {
                let mut far_shares = Rat::zero();
                for hinge in &self.incidence[&vertex] {
                    let far = self.hinges[hinge]
                        .far_endpoint(vertex)
                        .expect("an incident hinge names this vertex");
                    far_shares += &deviations[&far];
                }
                let carried = (&one - coefficient) * &deficits[&vertex] - coefficient * far_shares;
                (vertex, carried)
            })
            .collect()
    }

    /// Apply the update law once under a **declared** discharge coefficient.
    ///
    /// The coefficient is the caller's, and [`coefficient_species`] says exactly what it does to the
    /// total-curvature functional. [`Self::step`] is this at `c = 1`, which is
    /// [`CoefficientSpecies::Reflective`].
    pub fn step_at(&mut self, coefficient: &Rat) -> CurvatureFlowStep {
        let deficits_before = self.deficits();
        let traced_deviations = self.traced_deviations();
        let revisions = self.revisions_at(coefficient);
        self.apply(deficits_before, traced_deviations, revisions)
    }

    fn apply(
        &mut self,
        deficits_before: BTreeMap<VertexId, Rat>,
        traced_deviations: BTreeMap<VertexId, Rat>,
        revisions: BTreeMap<HingeId, Rat>,
    ) -> CurvatureFlowStep {
        for (id, revision) in &revisions {
            let carried = self
                .hinges
                .get_mut(id)
                .expect("the revision was keyed by a carried hinge");
            carried.response += revision;
        }
        let deficits_after = self.deficits();
        let total_deficit_before = deficits_before
            .values()
            .fold(Rat::zero(), |sum, deficit| sum + deficit);
        let total_deficit_after = deficits_after
            .values()
            .fold(Rat::zero(), |sum, deficit| sum + deficit);
        let moved = revisions.values().any(|revision| !revision.is_zero());
        CurvatureFlowStep {
            deficits_before,
            traced_deviations,
            revisions,
            deficits_after,
            total_deficit_before,
            total_deficit_after,
            moved,
        }
    }

    /// Apply the update law once at the module's derived `c = 1`.
    pub fn step(&mut self) -> CurvatureFlowStep {
        self.step_at(&Rat::from_integer(BigInt::from(1)))
    }

    /// The largest `|K(v)|` over the configuration — the pointwise amplitude the total cannot see.
    ///
    /// `Sigma K` is one linear functional. A configuration whose total is zero can still carry
    /// arbitrarily large opposing deficits, and on a bipartite incidence it does so forever at every
    /// coefficient. Reporting the total alone would be the receipt-over-implementation defect at the
    /// level of a convergence claim.
    pub fn deficit_amplitude(&self) -> Rat {
        self.deficits()
            .into_values()
            .map(|deficit| {
                if deficit < Rat::zero() {
                    -deficit
                } else {
                    deficit
                }
            })
            .fold(Rat::zero(), |carried, magnitude| {
                if magnitude > carried {
                    magnitude
                } else {
                    carried
                }
            })
    }

    /// The components and two-colouring of the hinge incidence.
    pub fn incidence_parity(&self) -> IncidenceParity {
        let mut component = BTreeMap::new();
        let mut parity = BTreeMap::new();
        let mut odd_cycle_components = BTreeSet::new();
        for root in self.vertices() {
            if component.contains_key(&root) {
                continue;
            }
            let mut members = vec![root];
            component.insert(root, root);
            parity.insert(root, true);
            let mut frontier = VecDeque::from([root]);
            let mut odd = false;
            while let Some(vertex) = frontier.pop_front() {
                let here = parity[&vertex];
                for hinge in &self.incidence[&vertex] {
                    let far = self.hinges[hinge]
                        .far_endpoint(vertex)
                        .expect("an incident hinge names this vertex");
                    match parity.get(&far) {
                        Some(known) => {
                            if *known == here {
                                odd = true;
                            }
                        }
                        None => {
                            parity.insert(far, !here);
                            component.insert(far, root);
                            members.push(far);
                            frontier.push_back(far);
                        }
                    }
                }
            }
            if odd {
                odd_cycle_components.insert(root);
                for member in members {
                    parity.remove(&member);
                }
            }
        }
        IncidenceParity {
            component,
            parity,
            odd_cycle_components,
        }
    }

    pub fn carries_odd_hinge_cycle(&self) -> bool {
        self.incidence_parity().carries_odd_hinge_cycle()
    }

    /// `t_C = FLAT_COORDINATION * (|A_C| - |B_C|) / (2 |E_C|)` per component,
    /// keyed by that component's least vertex; zero on a component carrying an
    /// odd hinge cycle.
    ///
    /// This is the scale the fixed-point characterization forces. It is
    /// computed from the bipartition and the hinge count alone — no response
    /// is read — so agreement with an observed traced deviation is evidence
    /// and not a restatement.
    pub fn forced_component_scale(&self) -> BTreeMap<VertexId, Rat> {
        let parity = self.incidence_parity();
        let mut parts: BTreeMap<VertexId, (usize, usize)> = BTreeMap::new();
        for vertex in self.vertices() {
            let key = parity.component[&vertex];
            let entry = parts.entry(key).or_insert((0, 0));
            match parity.parity.get(&vertex) {
                Some(true) => entry.0 += 1,
                Some(false) => entry.1 += 1,
                None => {}
            }
        }
        let mut hinge_counts: BTreeMap<VertexId, usize> = BTreeMap::new();
        for carried in self.hinges.values() {
            let key = parity.component[&carried.endpoints[0]];
            *hinge_counts.entry(key).or_insert(0) += 1;
        }
        parts
            .into_iter()
            .map(|(key, (left, right))| {
                if parity.odd_cycle_components.contains(&key) {
                    return (key, Rat::zero());
                }
                let hinges = hinge_counts.get(&key).copied().unwrap_or(0);
                let signed =
                    Rat::from_integer(BigInt::from(left as i64) - BigInt::from(right as i64));
                let scale = flat_coordination() * signed / (count(2) * count(hinges));
                (key, scale)
            })
            .collect()
    }

    /// Classify the configuration against the fixed-point characterization.
    pub fn fixed_point(&self) -> CurvatureFixedPoint {
        let revisions = self.revisions();
        let moving = revisions
            .into_iter()
            .filter(|(_, revision)| !revision.is_zero())
            .collect::<BTreeMap<_, _>>();
        if !moving.is_empty() {
            return CurvatureFixedPoint::Moving { revisions: moving };
        }
        if self.is_flat() {
            return CurvatureFixedPoint::Flat;
        }
        let parity = self.incidence_parity();
        let deviations = self.traced_deviations();
        let mut component_scale = BTreeMap::new();
        for vertex in self.vertices() {
            let key = parity.component[&vertex];
            if component_scale.contains_key(&key) {
                continue;
            }
            if key == vertex {
                component_scale.insert(key, deviations[&vertex].clone());
            }
        }
        CurvatureFixedPoint::AlternatingTracedDeviation { component_scale }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Edge, EventId, SimplicialComplex, VertexLinkClass};
    use num_traits::Signed;
    use relational_geometry::{integer, rat};

    fn vertex(id: u64) -> VertexId {
        VertexId(id)
    }

    fn hinge(id: u64) -> HingeId {
        HingeId(id)
    }

    /// Hinge incidence of a pentagonal bipyramid: two apexes of link size 5
    /// and five equator vertices of link size 4.
    ///
    /// The two distinct link sizes are the point of the fixture. A fixture in
    /// which every vertex has the same link size cannot show that the deficit
    /// varies with the link, and cannot distinguish the traced deviation from
    /// the raw deficit.
    fn bipyramid_hinges() -> Vec<(HingeId, [VertexId; 2])> {
        let north = vertex(1);
        let south = vertex(2);
        let equator: Vec<VertexId> = (0..5).map(|i| vertex(3 + i)).collect();
        let mut hinges = Vec::new();
        let mut next = 1_u64;
        for e in &equator {
            hinges.push((hinge(next), [north, *e]));
            next += 1;
        }
        for e in &equator {
            hinges.push((hinge(next), [south, *e]));
            next += 1;
        }
        for i in 0..5 {
            hinges.push((hinge(next), [equator[i], equator[(i + 1) % 5]]));
            next += 1;
        }
        hinges
    }

    fn bipyramid_apexes() -> [VertexId; 2] {
        [vertex(1), vertex(2)]
    }

    fn bipyramid_equator() -> Vec<VertexId> {
        (0..5).map(|i| vertex(3 + i)).collect()
    }

    /// The same bipyramid, with responses chosen so every deficit is exactly
    /// zero: apex hinges `6/5`, equator hinges `9/5`.
    ///
    /// Apex: `6 - 5*(6/5) = 0`. Equator: `6 - (2*(6/5) + 2*(9/5)) = 0`.
    /// The link sizes still differ and the responses still differ, so this is
    /// a flat configuration whose material could have moved.
    fn flat_bipyramid() -> DiscreteCurvatureConfiguration {
        DiscreteCurvatureConfiguration::found(
            bipyramid_hinges()
                .iter()
                .flat_map(|(_, endpoints)| *endpoints)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .map(|v| {
                    let degree = bipyramid_hinges()
                        .iter()
                        .filter(|(_, endpoints)| endpoints.contains(&v))
                        .count();
                    (v, degree)
                }),
            bipyramid_hinges().into_iter().map(|(id, endpoints)| {
                let apexes = bipyramid_apexes();
                let touches_apex = endpoints.iter().any(|v| apexes.contains(v));
                let response = if touches_apex { rat(6, 5) } else { rat(9, 5) };
                (id, endpoints, response)
            }),
        )
        .expect("the flat bipyramid is a well formed configuration")
    }

    /// A pentagonal bipyramid as an actual oriented simplicial complex, so the
    /// bridge to `local_star`'s `coordination_defect` can be checked against
    /// real simplicial incidence rather than asserted.
    fn bipyramid_complex() -> (SimplicialComplex, Vec<VertexId>) {
        let mut complex = SimplicialComplex::default();
        let event = EventId(1);
        let north = complex.found_vertex("north", event);
        let south = complex.found_vertex("south", event);
        let equator: Vec<VertexId> = (0..5)
            .map(|i| complex.found_vertex(format!("equator-{i}"), event))
            .collect();
        for i in 0..5 {
            let a = equator[i];
            let b = equator[(i + 1) % 5];
            complex
                .found_face(format!("north-{i}"), event, [north, a, b])
                .expect("the northern cap face is well formed");
            complex
                .found_face(format!("south-{i}"), event, [south, b, a])
                .expect("the southern cap face is well formed");
        }
        let mut vertices = vec![north, south];
        vertices.extend(equator);
        (complex, vertices)
    }

    /// `K_{2,3}`: three vertices of link size 2 against two of link size 3.
    /// Bipartite and unbalanced, so the fixed-point characterization predicts
    /// a nonzero forced scale.
    fn complete_bipartite_two_three(response: Rat) -> DiscreteCurvatureConfiguration {
        let left = [vertex(1), vertex(2), vertex(3)];
        let right = [vertex(4), vertex(5)];
        let mut hinges = Vec::new();
        let mut next = 1_u64;
        for a in left {
            for b in right {
                hinges.push((hinge(next), [a, b], response.clone()));
                next += 1;
            }
        }
        DiscreteCurvatureConfiguration::found(
            left.into_iter()
                .map(|v| (v, 2))
                .chain(right.into_iter().map(|v| (v, 3))),
            hinges,
        )
        .expect("K(2,3) is a well formed configuration")
    }

    fn triangle(responses: [Rat; 3]) -> DiscreteCurvatureConfiguration {
        let [a, b, c] = [vertex(1), vertex(2), vertex(3)];
        DiscreteCurvatureConfiguration::found(
            [(a, 2), (b, 2), (c, 2)],
            [
                (hinge(1), [a, b], responses[0].clone()),
                (hinge(2), [b, c], responses[1].clone()),
                (hinge(3), [c, a], responses[2].clone()),
            ],
        )
        .expect("the triangle is a well formed configuration")
    }

    fn four_cycle(response: Rat) -> DiscreteCurvatureConfiguration {
        let v = [vertex(1), vertex(2), vertex(3), vertex(4)];
        DiscreteCurvatureConfiguration::found(
            v.into_iter().map(|x| (x, 2)),
            (0..4).map(|i| {
                (
                    hinge(i as u64 + 1),
                    [v[i], v[(i + 1) % 4]],
                    response.clone(),
                )
            }),
        )
        .expect("the four cycle is a well formed configuration")
    }

    // ---------------------------------------------------------------
    // The bridge: the deficit at unit response IS local_star's charge.
    // ---------------------------------------------------------------

    #[test]
    fn unit_response_deficit_reproduces_the_local_star_coordination_charge() {
        let (complex, vertices) = bipyramid_complex();
        let mut link_sizes = Vec::new();
        for v in &vertices {
            let link = complex
                .vertex_star_link(*v)
                .expect("every bipyramid vertex has a link");
            assert_eq!(
                link.link_class,
                VertexLinkClass::Cycle,
                "every bipyramid vertex is an interior cycle, so local_star \
                 computes InteriorCycle{{charge}} there"
            );
            link_sizes.push((*v, link.link_vertices.len()));
        }

        // Control against a fixture whose material cannot vary the property:
        // the link sizes must take more than one value.
        let distinct = link_sizes
            .iter()
            .map(|(_, size)| *size)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            distinct,
            BTreeSet::from([4, 5]),
            "the fixture must carry more than one link size, or it cannot show \
             that the deficit varies with the link"
        );

        let configuration = DiscreteCurvatureConfiguration::at_unit_response(
            complex
                .faces
                .values()
                .flat_map(|face| {
                    let [a, b, c] = face.vertices;
                    [
                        Edge::new(a, b).expect("a face edge is well formed"),
                        Edge::new(b, c).expect("a face edge is well formed"),
                        Edge::new(c, a).expect("a face edge is well formed"),
                    ]
                })
                .collect::<BTreeSet<_>>()
                .into_iter()
                .enumerate()
                .map(|(index, edge)| (hinge(index as u64 + 1), [edge.lower, edge.upper])),
        )
        .expect("the bipyramid edge population is a well formed configuration");

        for (v, link_size) in &link_sizes {
            // This is `local_star.rs:1151` written out.
            let local_star_charge = 6_i64 - i64::try_from(*link_size).expect("fits");
            assert_eq!(
                configuration.deficit(*v).expect("carried vertex"),
                integer(local_star_charge),
                "vertex {v:?} of link size {link_size}"
            );
            assert_eq!(
                configuration
                    .combinatorial_charge(*v)
                    .expect("carried vertex"),
                local_star_charge
            );
        }

        // Discrete Gauss-Bonnet on a sphere: sum = 6 * chi = 12, provably nonzero.
        assert_eq!(configuration.total_deficit(), integer(12));
        assert!(!configuration.total_deficit().is_zero());
    }

    // ---------------------------------------------------------------
    // THE FALSIFIER, first half: a charged configuration MUST move.
    // ---------------------------------------------------------------

    #[test]
    fn a_charged_configuration_moves_under_the_flow() {
        let mut configuration =
            DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
                .expect("the unit bipyramid is well formed");

        // The nonzero control: this configuration's curvature is not merely
        // "some", it is exactly 12, and every single vertex is charged.
        assert_eq!(configuration.total_deficit(), integer(12));
        for apex in bipyramid_apexes() {
            assert_eq!(configuration.deficit(apex).expect("carried"), integer(1));
        }
        for e in bipyramid_equator() {
            assert_eq!(configuration.deficit(e).expect("carried"), integer(2));
        }
        assert!(matches!(
            configuration.fixed_point(),
            CurvatureFixedPoint::Moving { .. }
        ));

        let before = configuration.responses();
        let step = configuration.step();
        assert!(step.moved);

        // Every hinge moves, with the exact increment the law predicts:
        // apex hinges 1/5 + 1/2 = 7/10, equator hinges 1/2 + 1/2 = 1.
        assert_eq!(step.revisions.len(), 15);
        for revision in step.revisions.values() {
            assert!(!revision.is_zero(), "no hinge may sit still here");
        }
        let increments = step.revisions.values().cloned().collect::<BTreeSet<_>>();
        assert_eq!(increments, BTreeSet::from([rat(7, 10), integer(1)]));

        let after = configuration.responses();
        assert_ne!(before, after);
        for (id, response) in &after {
            assert_ne!(response, &before[id], "hinge {id:?} did not move");
        }

        // The successor deficits, exactly.
        for apex in bipyramid_apexes() {
            assert_eq!(step.deficits_after[&apex], rat(-5, 2));
        }
        for e in bipyramid_equator() {
            assert_eq!(step.deficits_after[&e], rat(-7, 5));
        }
        assert_eq!(step.total_deficit_before, integer(12));
        assert_eq!(step.total_deficit_after, integer(-12));
    }

    // ---------------------------------------------------------------
    // THE FALSIFIER, second half: a flat configuration MUST be fixed.
    // ---------------------------------------------------------------

    #[test]
    fn a_flat_configuration_is_left_exactly_fixed() {
        let mut configuration = flat_bipyramid();

        // The fixture must be able to move: its link sizes differ and its
        // responses differ. Flatness here is a property of the metric datum,
        // not an artefact of a uniform fixture.
        let link_sizes = configuration
            .vertices()
            .map(|v| configuration.link_size(v).expect("carried"))
            .collect::<BTreeSet<_>>();
        assert_eq!(link_sizes, BTreeSet::from([4, 5]));
        let responses = configuration
            .responses()
            .into_values()
            .collect::<BTreeSet<_>>();
        assert_eq!(responses, BTreeSet::from([rat(6, 5), rat(9, 5)]));

        assert!(configuration.is_flat());
        assert_eq!(configuration.total_deficit(), Rat::zero());
        assert_eq!(configuration.fixed_point(), CurvatureFixedPoint::Flat);

        let before = configuration.responses();
        let step = configuration.step();
        assert!(
            !step.moved,
            "a flow that moves a flat configuration is introducing curvature, \
             not responding to it"
        );
        for revision in step.revisions.values() {
            assert!(revision.is_zero());
        }
        assert_eq!(configuration.responses(), before);
        assert_eq!(step.deficits_after, step.deficits_before);
        assert_eq!(step.total_deficit_after, Rat::zero());

        // Ten further steps change nothing.
        for _ in 0..10 {
            let step = configuration.step();
            assert!(!step.moved);
        }
        assert_eq!(configuration.responses(), before);
    }

    // ---------------------------------------------------------------
    // Total curvature: negated by one step, preserved by two.
    // ---------------------------------------------------------------

    #[test]
    fn total_curvature_is_negated_each_step_and_preserved_by_the_doubled_flow() {
        let mut configuration =
            DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
                .expect("the unit bipyramid is well formed");
        let founding_total = configuration.total_deficit();
        assert_eq!(founding_total, integer(12));

        let mut totals = vec![founding_total.clone()];
        let mut apex_deficits = vec![
            configuration
                .deficit(bipyramid_apexes()[0])
                .expect("carried"),
        ];
        for _ in 0..6 {
            let step = configuration.step();
            assert_eq!(
                step.total_deficit_after,
                -step.total_deficit_before.clone(),
                "one step negates the total exactly"
            );
            assert_eq!(
                step.total_deficit_after.abs(),
                founding_total.abs(),
                "the magnitude of the total is preserved exactly"
            );
            totals.push(step.total_deficit_after.clone());
            apex_deficits.push(
                configuration
                    .deficit(bipyramid_apexes()[0])
                    .expect("carried"),
            );
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
            ]
        );
        // The doubled flow preserves it outright.
        for pair in totals.windows(3) {
            assert_eq!(pair[0], pair[2]);
        }
        // Control against a no-op flow passing this test vacuously: the local
        // deficits genuinely change, they are not merely re-signed.
        assert_eq!(
            apex_deficits[0..3].to_vec(),
            vec![integer(1), rat(-5, 2), rat(7, 4)]
        );
        assert!(
            apex_deficits.iter().collect::<BTreeSet<_>>().len() > 3,
            "the apex deficit must actually vary along the flow"
        );
    }

    #[test]
    fn gauss_bonnet_is_preserved_outright_exactly_when_the_total_is_zero() {
        // K(2,3) at response 5/2 has total deficit zero; there the negation is
        // preservation, and it holds for the same reason the sphere's does not.
        let mut configuration = complete_bipartite_two_three(rat(5, 2));
        assert_eq!(configuration.total_deficit(), Rat::zero());
        let step = configuration.step();
        assert_eq!(step.total_deficit_after, step.total_deficit_before);

        // Whereas the sphere's 12 is not preserved, and that is the module's
        // declared departure from a Gauss-Bonnet-preserving flow.
        let mut sphere = DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
            .expect("the unit bipyramid is well formed");
        let step = sphere.step();
        assert_ne!(step.total_deficit_after, step.total_deficit_before);
        assert_eq!(step.total_deficit_after, -step.total_deficit_before);
    }

    // ---------------------------------------------------------------
    // Fixed points.
    // ---------------------------------------------------------------

    #[test]
    fn an_unbalanced_bipartite_component_carries_a_nonflat_fixed_point() {
        let mut configuration = complete_bipartite_two_three(rat(5, 2));

        // Nonzero control: this is fixed, and it is emphatically NOT flat.
        // Every vertex carries a nonzero deficit.
        for v in configuration.vertices() {
            assert!(
                !configuration.deficit(v).expect("carried").is_zero(),
                "vertex {v:?} must be charged, or this proves nothing"
            );
        }
        assert!(!configuration.is_flat());
        assert_eq!(
            configuration.deficit(vertex(1)).expect("carried"),
            integer(1)
        );
        assert_eq!(
            configuration.deficit(vertex(4)).expect("carried"),
            rat(-3, 2)
        );

        // And it does not move.
        let before = configuration.responses();
        let step = configuration.step();
        assert!(!step.moved);
        assert_eq!(configuration.responses(), before);

        let classification = configuration.fixed_point();
        match &classification {
            CurvatureFixedPoint::AlternatingTracedDeviation { component_scale } => {
                assert_eq!(component_scale.len(), 1);
                assert_eq!(component_scale[&vertex(1)], rat(1, 2));
            }
            other => panic!("expected a nonflat fixed point, got {other:?}"),
        }

        // The forced scale, computed from the bipartition and the hinge count
        // alone, agrees with the traced deviation the responses produced.
        let forced = configuration.forced_component_scale();
        assert_eq!(forced[&vertex(1)], rat(1, 2));
        assert_eq!(
            configuration.traced_deviation(vertex(1)).expect("carried"),
            forced[&vertex(1)]
        );
        assert_eq!(
            configuration.traced_deviation(vertex(4)).expect("carried"),
            -forced[&vertex(1)].clone()
        );
    }

    #[test]
    fn the_forced_scale_is_counting_and_predicts_which_incidences_admit_nonflat_fixed_points() {
        // Unbalanced bipartite: 6*(3-2)/(2*6) = 1/2.
        let unbalanced = complete_bipartite_two_three(integer(1));
        assert_eq!(
            unbalanced.forced_component_scale()[&vertex(1)],
            rat(1, 2),
            "the forced scale is a property of the incidence, not of the responses"
        );

        // Balanced bipartite (four cycle): 6*(2-2)/(2*4) = 0, so only flat is
        // fixed there, exactly like an odd cycle and for a different reason.
        let balanced = four_cycle(integer(1));
        assert_eq!(balanced.forced_component_scale()[&vertex(1)], Rat::zero());
        assert!(!balanced.carries_odd_hinge_cycle());

        // A charged four cycle therefore moves, despite being bipartite.
        let mut charged = four_cycle(integer(2));
        for v in charged.vertices() {
            assert_eq!(charged.deficit(v).expect("carried"), integer(2));
        }
        assert!(charged.step().moved);

        // And a flat four cycle is fixed.
        let mut flat = four_cycle(integer(3));
        assert!(flat.is_flat());
        assert!(!flat.step().moved);

        // Odd cycle: forced scale zero because the component admits no
        // two-colouring at all.
        let odd = triangle([integer(1), integer(1), integer(1)]);
        assert!(odd.carries_odd_hinge_cycle());
        assert_eq!(odd.forced_component_scale()[&vertex(1)], Rat::zero());
    }

    #[test]
    fn a_component_carrying_an_odd_hinge_cycle_is_fixed_only_when_flat() {
        // Exhaustive over 6^3 = 216 integer triangles. The characterization
        // says: fixed if and only if flat, and flat forces every response to 3.
        let mut fixed = Vec::new();
        let mut moving = 0_usize;
        for a in 0..6_i64 {
            for b in 0..6_i64 {
                for c in 0..6_i64 {
                    let configuration = triangle([integer(a), integer(b), integer(c)]);
                    let is_fixed = matches!(
                        configuration.fixed_point(),
                        CurvatureFixedPoint::Flat
                            | CurvatureFixedPoint::AlternatingTracedDeviation { .. }
                    );
                    assert_eq!(
                        is_fixed,
                        configuration.is_flat(),
                        "triangle ({a},{b},{c}) violates the odd-cycle characterization"
                    );
                    if is_fixed {
                        fixed.push((a, b, c));
                    } else {
                        moving += 1;
                    }
                }
            }
        }
        // Both halves are populated, so neither branch passed vacuously.
        assert_eq!(fixed, vec![(3, 3, 3)]);
        assert_eq!(moving, 215);
    }

    #[test]
    fn a_charged_odd_cycle_moves_and_returns_the_predicted_deficits() {
        let mut configuration = triangle([integer(3), integer(3), integer(4)]);
        assert_eq!(
            configuration.deficit(vertex(1)).expect("carried"),
            integer(-1)
        );
        assert_eq!(
            configuration.deficit(vertex(2)).expect("carried"),
            Rat::zero()
        );
        assert_eq!(
            configuration.deficit(vertex(3)).expect("carried"),
            integer(-1)
        );
        assert_eq!(configuration.total_deficit(), integer(-2));
        let step = configuration.step();
        assert!(step.moved);
        assert_eq!(step.deficits_after[&vertex(1)], rat(1, 2));
        assert_eq!(step.deficits_after[&vertex(2)], integer(1));
        assert_eq!(step.deficits_after[&vertex(3)], rat(1, 2));
        assert_eq!(step.total_deficit_after, integer(2));
    }

    // ---------------------------------------------------------------
    // The closed form is an independent route to the same successor.
    // ---------------------------------------------------------------

    #[test]
    fn the_closed_form_successor_agrees_with_recomputation_after_the_step() {
        // Deliberately asymmetric responses over a fixture with two link sizes,
        // so neither the degrees nor the responses are uniform.
        let hinges = bipyramid_hinges();
        let mut degrees: BTreeMap<VertexId, usize> = BTreeMap::new();
        for (_, endpoints) in &hinges {
            for v in endpoints {
                *degrees.entry(*v).or_insert(0) += 1;
            }
        }
        let mut configuration = DiscreteCurvatureConfiguration::found(
            degrees,
            hinges
                .iter()
                .enumerate()
                .map(|(index, (id, endpoints))| (*id, *endpoints, rat(index as i64 + 1, 7))),
        )
        .expect("the asymmetric bipyramid is well formed");

        // Control: the material varies, so this is not agreement on a constant.
        let distinct = configuration
            .deficits()
            .into_values()
            .collect::<BTreeSet<_>>();
        assert!(
            distinct.len() >= 5,
            "the fixture must return at least five distinct deficits, got {}",
            distinct.len()
        );

        for _ in 0..4 {
            let predicted = configuration.predicted_deficits();
            let step = configuration.step();
            assert_eq!(
                predicted, step.deficits_after,
                "the closed form and the recomputation must agree exactly"
            );
            let distinct = predicted.into_values().collect::<BTreeSet<_>>();
            assert!(distinct.len() >= 2, "the successor deficits must vary too");
            assert!(step.moved);
        }
    }

    #[test]
    fn the_single_hinge_revision_agrees_with_the_batch_revisions() {
        // Two implementations of the same law: `hinge_revision` reaches the
        // traced deviations one vertex at a time, `revisions` builds the whole
        // map first. They must agree on a fixture with varying link sizes and
        // varying responses.
        let hinges = bipyramid_hinges();
        let mut degrees: BTreeMap<VertexId, usize> = BTreeMap::new();
        for (_, endpoints) in &hinges {
            for v in endpoints {
                *degrees.entry(*v).or_insert(0) += 1;
            }
        }
        let configuration = DiscreteCurvatureConfiguration::found(
            degrees,
            hinges
                .iter()
                .enumerate()
                .map(|(index, (id, endpoints))| (*id, *endpoints, rat(index as i64 + 1, 3))),
        )
        .expect("the asymmetric bipyramid is well formed");
        let batch = configuration.revisions();
        assert_eq!(batch.len(), 15);
        let distinct = batch.values().cloned().collect::<BTreeSet<_>>();
        assert!(
            distinct.len() >= 5,
            "the revisions must vary, or agreement proves nothing"
        );
        for hinge in configuration.hinges() {
            assert_eq!(
                configuration.hinge_revision(hinge.id).expect("carried"),
                batch[&hinge.id]
            );
        }
    }

    #[test]
    fn the_traced_deviation_is_the_deficit_divided_by_the_actual_link_size() {
        let configuration = DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
            .expect("the unit bipyramid is well formed");
        // Apex: deficit 1 over link size 5. Equator: deficit 2 over link size 4.
        assert_eq!(
            configuration
                .traced_deviation(bipyramid_apexes()[0])
                .expect("carried"),
            rat(1, 5)
        );
        assert_eq!(
            configuration
                .traced_deviation(bipyramid_equator()[0])
                .expect("carried"),
            rat(1, 2)
        );
        // The two differ, so a law that forgot the division would be visible.
        assert_ne!(
            configuration
                .traced_deviation(bipyramid_apexes()[0])
                .expect("carried"),
            configuration
                .deficit(bipyramid_apexes()[0])
                .expect("carried")
        );
    }

    // ---------------------------------------------------------------
    // Refusals.
    // ---------------------------------------------------------------

    #[test]
    fn the_carrier_refuses_the_configurations_its_proofs_exclude() {
        let isolated = DiscreteCurvatureConfiguration::found(
            [(vertex(1), 1), (vertex(2), 1), (vertex(3), 0)],
            [(hinge(1), [vertex(1), vertex(2)], integer(1))],
        );
        assert_eq!(
            isolated,
            Err(DiscreteCurvatureError::IsolatedVertex(vertex(3)))
        );

        let self_incident = DiscreteCurvatureConfiguration::found(
            [(vertex(1), 2)],
            [(hinge(1), [vertex(1), vertex(1)], integer(1))],
        );
        assert_eq!(
            self_incident,
            Err(DiscreteCurvatureError::SelfIncidentHinge {
                hinge: hinge(1),
                vertex: vertex(1),
            })
        );

        let miscounted = DiscreteCurvatureConfiguration::found(
            [(vertex(1), 3), (vertex(2), 1)],
            [(hinge(1), [vertex(1), vertex(2)], integer(1))],
        );
        assert_eq!(
            miscounted,
            Err(
                DiscreteCurvatureError::DeclaredLinkSizeDisagreesWithIncidence {
                    vertex: vertex(1),
                    declared: 3,
                    incident: 1,
                }
            )
        );

        let unknown = DiscreteCurvatureConfiguration::found(
            [(vertex(1), 1)],
            [(hinge(1), [vertex(1), vertex(9)], integer(1))],
        );
        assert_eq!(
            unknown,
            Err(DiscreteCurvatureError::UnknownHingeEndpoint {
                hinge: hinge(1),
                vertex: vertex(9),
            })
        );

        let duplicate = DiscreteCurvatureConfiguration::found(
            [(vertex(1), 2), (vertex(2), 2)],
            [
                (hinge(1), [vertex(1), vertex(2)], integer(1)),
                (hinge(1), [vertex(2), vertex(1)], integer(1)),
            ],
        );
        assert_eq!(
            duplicate,
            Err(DiscreteCurvatureError::DuplicateHinge(hinge(1)))
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The discharge coefficient: the total law, the annihilator, and the bipartite obstruction
    // ---------------------------------------------------------------------------------------------

    /// `Sigma K' = (1 - 2c) Sigma K` holds exactly at every declared coefficient.
    ///
    /// This is the theorem the module's `c = 1` is one point of, and it is what makes `c = 1` a
    /// reflection rather than a flow. Checked on real material at six coefficients, over exact
    /// rationals, with no tolerance anywhere.
    #[test]
    fn the_total_curvature_multiplier_is_exactly_one_minus_two_c() {
        for (numerator, denominator) in [(0, 1), (1, 4), (1, 2), (3, 4), (1, 1), (2, 1)] {
            let coefficient = rat(numerator, denominator);
            let mut configuration =
                DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
                    .expect("the bipyramid founds");
            let before = configuration.total_deficit();
            let step = configuration.step_at(&coefficient);
            let expected = total_multiplier(&coefficient) * &before;
            assert_eq!(
                step.total_deficit_after, expected,
                "coefficient {numerator}/{denominator}"
            );
            assert_eq!(step.total_deficit_before, before);
        }
    }

    /// The closed form and the response route agree at a general coefficient, not only at `c = 1`.
    #[test]
    fn the_predicted_and_enacted_successors_agree_at_every_coefficient() {
        for (numerator, denominator) in [(1, 3), (1, 2), (1, 1), (5, 4)] {
            let coefficient = rat(numerator, denominator);
            let mut configuration =
                DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
                    .expect("the bipyramid founds");
            let predicted = configuration.predicted_deficits_at(&coefficient);
            let step = configuration.step_at(&coefficient);
            assert_eq!(
                predicted, step.deficits_after,
                "coefficient {numerator}/{denominator}"
            );
        }
    }

    /// `c = 1/2` annihilates the total in exactly one step, and it is the only coefficient that does.
    #[test]
    fn the_derived_annihilator_zeroes_the_total_in_one_step() {
        let mut configuration =
            DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
                .expect("the bipyramid founds");
        assert!(
            !configuration.total_deficit().is_zero(),
            "the fixture is curved to begin with"
        );
        let step = configuration.step_at(&dissipative_annihilator());
        assert!(step.total_deficit_after.is_zero());
        assert_eq!(
            coefficient_species(&dissipative_annihilator()),
            CoefficientSpecies::Annihilating
        );
        assert_eq!(
            coefficient_species(&rat(1, 1)),
            CoefficientSpecies::Reflective,
            "the module's own derived law is the reflection"
        );
    }

    /// **The flow contracts the total and the reflection does not**, over the same material and the
    /// same number of steps, exactly and with the ratio exhibited.
    ///
    /// Stated on the total and **not** on the pointwise amplitude, because the total is what
    /// [`total_multiplier`] governs and the amplitude is not. On this fixture the reflective
    /// amplitude in fact decays even though its total never does — the two quantities are
    /// independent, and asserting a direction for the amplitude would be a claim this module has
    /// not derived. The driver reports the amplitude; the theorem is the total.
    #[test]
    fn a_dissipative_coefficient_contracts_the_total_and_the_reflective_one_only_alternates() {
        let steps = 6;
        let quarter = rat(1, 4);
        let one = rat(1, 1);

        // c = 1/4 gives multiplier 1/2: the total halves, exactly, every step.
        let mut dissipative =
            DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges()).expect("founds");
        let start = dissipative.total_deficit();
        assert!(!start.is_zero(), "the fixture is curved to begin with");
        let mut carried = start.clone();
        for index in 0..steps {
            dissipative.step_at(&quarter);
            carried = rat(1, 2) * carried;
            assert_eq!(dissipative.total_deficit(), carried, "step {index}");
        }
        assert_eq!(
            dissipative.total_deficit(),
            &start * rat(1, 64),
            "six halvings, exactly"
        );

        // c = 1 gives multiplier -1: the magnitude never moves and the sign alternates.
        let mut reflective =
            DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges()).expect("founds");
        for index in 0..steps {
            reflective.step_at(&one);
            let expected = if index % 2 == 0 {
                -start.clone()
            } else {
                start.clone()
            };
            assert_eq!(reflective.total_deficit(), expected, "step {index}");
        }
        assert_eq!(reflective.total_deficit().abs(), start.abs());

        // And the annihilator reaches zero in one step and stays.
        let mut annihilating =
            DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges()).expect("founds");
        for _ in 0..steps {
            annihilating.step_at(&dissipative_annihilator());
            assert!(annihilating.total_deficit().is_zero());
        }
    }

    /// **The bipartite obstruction, exactly.** On a single hinge the alternating deficit is an
    /// eigenvector of the flow with eigenvalue `1` at EVERY coefficient, so no choice of `c`
    /// dissipates it. Two-colourability is the obstruction to convergence, which is the hand again.
    #[test]
    fn an_alternating_deficit_on_a_bipartite_incidence_is_invariant_at_every_coefficient() {
        for (numerator, denominator) in [(1, 4), (1, 2), (3, 4), (1, 1)] {
            let coefficient = rat(numerator, denominator);
            // Two vertices, one hinge. Unequal link sizes are impossible here, so the deficits are
            // equal and opposite only if the responses make them so: K(u) = 6 - r, K(v) = 6 - r.
            // Instead take the bipyramid's own two-colouring, which the module already detects.
            let mut configuration =
                DiscreteCurvatureConfiguration::at_unit_response(bipartite_hinges())
                    .expect("the path founds");
            let before = configuration.deficits();
            configuration.step_at(&coefficient);
            let after = configuration.deficits();
            let alternating_before: Rat =
                before
                    .iter()
                    .enumerate()
                    .fold(Rat::zero(), |carried, (index, (_, deficit))| {
                        if index % 2 == 0 {
                            carried + deficit
                        } else {
                            carried - deficit
                        }
                    });
            let alternating_after: Rat =
                after
                    .iter()
                    .enumerate()
                    .fold(Rat::zero(), |carried, (index, (_, deficit))| {
                        if index % 2 == 0 {
                            carried + deficit
                        } else {
                            carried - deficit
                        }
                    });
            assert_eq!(
                alternating_before, alternating_after,
                "the alternating mode is invariant at coefficient {numerator}/{denominator}"
            );
        }
    }

    /// **On a regular component the annihilator reaches exact flatness in one step, and that is a
    /// property of the incidence rather than of the flow.**
    ///
    /// At unit response `K(v) = F - n_v`, so on a `d`-regular component `K` is constant `F - d` and
    /// `sum over neighbours of K(w)/n_w = d (F - d)/d = K(v)`. Hence at `c = 1/2`
    /// `K'(v) = (1/2)(K(v) - K(v)) = 0` exactly, everywhere, after one step.
    ///
    /// Stated here so that a driver reporting `FLAT after 1 step` on clique-like material cannot be
    /// read as a discovery about the coefficient. `CLAUDE.md` §8: a receipt that could not have come
    /// out otherwise carries no evidence. The irregular control is the second half of this test.
    #[test]
    fn the_annihilator_flattens_a_regular_component_in_one_step_and_an_irregular_one_not_at_all() {
        // K4: every vertex has link size 3.
        let mut regular_hinges = Vec::new();
        let mut next = 1_u64;
        for left in 1..=4u64 {
            for right in (left + 1)..=4u64 {
                regular_hinges.push((hinge(next), [vertex(left), vertex(right)]));
                next += 1;
            }
        }
        let mut regular = DiscreteCurvatureConfiguration::at_unit_response(regular_hinges)
            .expect("the tetrahedron founds");
        assert!(!regular.is_flat(), "K4 at unit response is curved");
        regular.step_at(&dissipative_annihilator());
        assert!(
            regular.is_flat(),
            "one step flattens a regular component exactly"
        );

        // The bipyramid is irregular — link sizes 5 and 4 — so the same coefficient zeroes the
        // total and leaves the configuration curved.
        let mut irregular = DiscreteCurvatureConfiguration::at_unit_response(bipyramid_hinges())
            .expect("the bipyramid founds");
        irregular.step_at(&dissipative_annihilator());
        assert!(
            irregular.total_deficit().is_zero(),
            "the total is annihilated regardless"
        );
        assert!(
            !irregular.is_flat(),
            "but an irregular component is not flattened, so the one-step result is about the \
             incidence and not about the coefficient"
        );
    }

    /// A path on three vertices: bipartite, so it carries the alternating mode above.
    fn bipartite_hinges() -> Vec<(HingeId, [VertexId; 2])> {
        vec![
            (hinge(1), [vertex(1), vertex(2)]),
            (hinge(2), [vertex(2), vertex(3)]),
        ]
    }
}
