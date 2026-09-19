//! **One Holonic Interaction chain, read as one tube: `|source⟩ → medium → neck → medium →
//! ⟨perspective|`.**
//!
//! [definition] This module is the **join** named by issue #4 and by
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md` under "First
//! consuming return with T8". It founds no fifth object. A chain here is **one**
//! [`crate::holonic_interaction::HolonicInteraction`] whose two media communicate only through
//! their coupling, and every reading below — the neck's section, the power current, the jet
//! staircase, the three widths, the interface condition and the reversal — is computed from that
//! single unit's own dynamics `A = (Ω − M)G`. Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Transport/HolonicChain.lean`
//! (namespace `Soma.Holonics.Transport.HolonicChain`), and the correspondence is the deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `crossBlock`, `upstreamPort`, `downstreamPort` | [`HolonicChain::cross_block`] and [`NeckCoupling`] |
//! | `OnUpstream`, `OnDownstream` | [`HolonicChain::over`], which refuses a chain whose ports are not separated |
//! | `port_transfer_is_the_cross_block`, `mul_onUpstream`, `onDownstream_mul` | [`HolonicChain::transfer_at`] |
//! | `cross_block_of_inverse`, `resolvent_cross_block` | the same reading's resolvent block |
//! | `transfer_factors_through_the_neck`, `transfer_rank_le_neck_rank` | [`HolonicChain::rank_bound`] and [`RankBoundReading`] |
//! | `pinhole_transfer_rank_le_one` | [`NeckCoupling::is_pinhole`] |
//! | `cross_block_pow_eq_zero_of_closed`, `markov_eq_zero_of_closed_neck` | [`HolonicChain::markov`] on a closed neck, and [`crate::neck::NeckReading::Closed`] |
//! | `markov`, `markov_zero_of_separated_ports`, `markov_one_eq_neck_product` | [`HolonicChain::markov`] and [`MarkovStaircase`] |
//! | `markov_is_the_separating_atlas_parameter` | the same reading: this owner founds no second notion of `C Aᵏ B` |
//! | `relative_degree_of_a_chain_is_at_least_one`, `markov_one_rank_le_neck_rank` | [`MarkovStaircase::relative_degree`] |
//! | `partialResolvent`, `partialResolvent_succ`, `resolvent_telescope` | [`HolonicChain::telescope_residual`] |
//! | `markov_are_the_expansion_coefficients`, `transfer_expansion_with_remainder` | the same reading's returned remainder |
//! | `storageRate`, `portPower`, `flow`, `skew_quad_eq_zero` | [`PowerStations`] |
//! | `port_power_balance`, `port_power_balance_faces` | [`PowerStations::transport_residual`] and [`PowerStations::face_power`] |
//! | `neck_power_jump_is_twice_the_cross_dissipation` | [`PowerStations::neck_jump`] |
//! | `power_current_is_continuous_across_a_lossless_neck` | the same jump at a lossless neck |
//! | `adjoint_is_the_reversed_structure`, `reversal_preserves_the_storage_rate` | [`ReversalReading`] |
//! | `no_direction_undoes_the_dissipation` | [`ReversalReading::dissipation_is_even`] |
//! | `reciprocity_of_the_reversed_chain`, `reversal_preserves_the_transfer_rank` | [`ReversalReading::reciprocal`] |
//!
//! # 1. The neck is the rank of the coupling between consecutive media
//!
//! [proved-derived; formal-checked; implemented-exact] Split the joint chart into the upstream
//! medium's coordinates and the downstream medium's. The generator's `(downstream, upstream)`
//! block `A₂₁` is **the neck**. From `N X = 1` alone — that is, from the second block row of the
//! resolvent identity, with no Schur complement formed — the resolvent's own cross block is
//! `X₂₁ = N₂₂⁻¹ A₂₁ X₁₁`, so with a rank factorization `A₂₁ = U V` of inner width `r`
//!
//! ```text
//!   H(s) = C X B = (C₂ N₂₂⁻¹ U) · (V X₁₁ B₁),      rank H(s) ≤ r
//! ```
//!
//! at every `s` off the poles. Many modes inside each medium, `r` channels at the interface, many
//! modes again: that is convergence into the neck and divergence out of it, exactly. `r = 1` is
//! the **pinhole**.
//!
//! [agent-inferred] Two corrections to the proposed law, inferred from `portGenerator`'s own
//! algebra rather than from the contract:
//!
//! 1. The one-directional product form `C₂(sI−A₂₂)⁻¹U · V(sI−A₁₁)⁻¹B₁` requires `A₁₂ = 0`, which a
//!    **port-Hamiltonian coupling never satisfies**: the interconnection places `K` at `Ω[to,from]`
//!    and `−Kᵀ` at `Ω[from,to]` at once, and a dissipative contact face is symmetric. The
//!    bidirectional statement above is therefore the operative one, and it needs no Schur
//!    complement: `X₁₁` already carries the feedback.
//! 2. The neck's rank is the rank of `A₂₁ = (Ω₂₁ − M₂₁) G₁`, **not** of `Ω₂₁ − M₂₁` alone. A
//!    singular upstream storage form lowers it further, and [`NeckCoupling`] returns both numbers
//!    so the two are never confused.
//!
//! # 2. Flux along the chain is the power current
//!
//! [proved-derived; formal-checked; implemented-exact] With `E_G = ½⟨x, Gx⟩` and `ẋ = Ax + Bu`,
//!
//! ```text
//!   Ė_G = ⟨u, Bᵀ G x⟩ − ⟨Gx, M Gx⟩
//! ```
//!
//! — injected port power minus dissipated power, the skew structure contributing exactly nothing.
//! [`PowerStations`] resolves that identity into a **five-station power current** whose values are
//! computed from the generator's own blocks and whose gap sources are computed from the block
//! storage rates and the face dissipation, independently:
//!
//! ```text
//!   Φ₀ = ⟨u, BᵀGx⟩                     the source port
//!   Φ₁ = −⟨(Gx)_up,   A₁₂ x_down⟩      leaving the upstream medium
//!   Φ₂ =  ⟨(Gx)_down, A₂₁ x_up⟩        entering the downstream medium
//!   Φ₃ = −⟨(Gx)_down, A₂ᴿ x_R⟩         leaving the downstream medium
//!   Φ₄ = the power delivered to the receiver's own block
//! ```
//!
//! and `σ_i = Φ_{i+1} − Φ_i` recomputed as `−(block storage rate + block dissipation)` at the two
//! media and as `−2⟨(Gx)_up, M_c (Gx)_down⟩` at the neck. **Across a lossless neck the power
//! current is continuous**, and its jump is exactly twice the cross dissipation — that is the sink
//! `σ` [`crate::neck::TubeProfile::station_balance`] consumes, and this owner does not re-implement
//! either that balance or [`crate::holonic_interaction::ContactDissipation::power_by_face`].
//! [`PowerStations::transport_residual`] is `injected − Σ storage − Σ dissipation`, returned as an
//! exact rational and never rounded.
//!
//! [agent-inferred] The **section** of a chain station is the rank of the linear map the chain's
//! signal factors through there — `rank B` at the source port, `rank G` at a medium, `rank A₂₁` at
//! the neck, `rank C` at the receiver port. This is inferred from §1: it is the only reading of
//! "cross-section" under which "many modes → `r` channels → many modes" is a statement about the
//! tube's area rather than a metaphor. Nothing here is declared by hand.
//!
//! # 3. The jet staircase at the neck is the chain's Markov staircase
//!
//! [proved-derived; formal-checked; implemented-exact] `h⁽ᵏ⁾(0) = C Aᵏ B` are exact rationals, and
//! the jet coefficients `c_k = C Aᵏ B / k!` enter [`crate::jet_staircase::FiniteJet`] directly.
//! The parameter itself is **already owned in Lean** by
//! `Foundation/ReceiverAtlas.lean::SeparatingAtlas.markov`, and the chain's is that one at the
//! joint index type — `markov_is_the_separating_atlas_parameter` records the agreement. This owner
//! has not composed a *Rust* Markov owner because there is none: the prior-art search
//! `prior-art 'HolonicChain|holonic_chain|Markov parameter|relative degree|neck rank|cross-domain
//! transfer'` returns `receiver_atlas.rs` only through its correspondence table, which cites the
//! Lean name without implementing it.
//! `C B = 0` for a chain whose ports are separated, so **the relative degree of a chain is at
//! least one**, and [`crate::neck::jet_order_at_neck`] reads the order from that jet.
//!
//! [agent-inferred] The proposal that "a storage-mediated coupling adds integrations and a
//! dissipative coupling adds fewer" is **not what the arithmetic gives**, and this owner refuses
//! to assert it. The relative degree is the least `k` with `C₂ (Aᵏ)₂₁ B₁ ≠ 0`; a skew coupling and
//! a dissipative contact face both put a nonzero block at `k = 1`, so both give relative degree
//! one whenever the perspective reads the coordinates the neck feeds. What moves the degree is
//! **where the perspective reads inside the downstream medium**, and the module's tests exhibit
//! one neck and one source whose relative degree is `1`, `2` and `3` as the aperture moves. The
//! increment is therefore computed per instance; no universal increment is available and none is
//! claimed.
//!
//! # 4. Interface condition and irreversibility
//!
//! [implemented-exact] [`HolonicChain::interface_reading`] is
//! [`crate::holonic_interaction::InterfaceReading`] at the neck over a three-node control complex:
//! tangential agreement with the normal jump equal to the source on the joint, computed by
//! [`crate::junction_law::check_junction`]. [`HolonicChain::neck_tube`] hands the profile to
//! [`crate::neck::NeckTube`], and [`HolonicChain::neck_holonomy`] takes
//! `continuing_tube::check_circuit_holonomy` — the call
//! [`crate::neck::NeckTube::holonomy_around_the_neck`] itself makes — around [`NECK_STATION`]
//! rather than around the profile's `argmin`, which a one-port source can move. The identity is a
//! lossless chain; a circuit defect is a dissipative one.
//!
//! [proved-derived; formal-checked] **What reversal does and does not do.** `((Ω−M)G)ᵀ = G((−Ω)−M)`:
//! transposing a chain reverses the conservative structure and leaves the dissipative one alone.
//! Hence the rate form `−2GMG` is **even** under reversal, the dissipated power is unchanged, and
//! the reversed chain still decays. The transfer of the adjoint chain is `H(s)ᵀ`, so the rank
//! bound, the poles and the analytic width are reversal-symmetric. The odd readings are the
//! station fluxes' sign (`TubeProfile::reversed` negates the current density) and the holonomy
//! defect's orientation bit. That pair is the first exact datum about the entropy direction along
//! an oriented chain; it is recorded as such and **does not close issue #5**, which asks for the
//! crossing of the time and entropy axes and needs the longitudinal axis of T5 as well.
//!
//! # 5. The consumer: a protein hinge is a neck between two media
//!
//! [implemented-exact] [`elastic_chain`] builds the chain from
//! [`crate::rigidity_receiver::RigidityJacobian`] with `Ω = 0`, `G = I` and `M = JᵀJ`: **every
//! rigidity constraint row is a contact face** with slip map that row and unit response, so the
//! faces are derived from measured constraints rather than declared, which closes the open
//! obligation `holonic_interaction.rs` recorded when its faces were hand-declared. A declared cut
//! partitions the sites into two domains; constraints inside a domain are that medium's faces,
//! constraints crossing the cut are the neck, and the neck's section is the rank of the
//! cross-domain stiffness block. [`hinge_by_minimal_section`] scans candidate cuts **within a
//! declared bound** and returns [`HingeSearch`], whose reading is
//! [`HingeVerdict::NotDecidedWithinBound`] when the scan did not exhaust the site population: a
//! finite prefix never proves a universal claim.
//!
//! # Floats
//!
//! [implemented-exact] Every carried and deciding value is an exact `Rat`. No `f32`, no `f64` and
//! no float literal appears on any path of this owner or of its tests; the only wall-clock number
//! is an `as_secs_f64` inside a test's `eprintln!` receipt, which decides nothing.
//!
//! # Sizes
//!
//! [definition] Every declared size is bounded before the work it sizes, against the ceilings
//! below, in the convention `holonic_interaction.rs` and `neck.rs` already use.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::algebraic::CausalCellId;
use crate::causal_chord::{ChordRefusal, PoleAtlas, PoleReading};
use crate::continuing_tube::check_circuit_holonomy;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::holonic_interaction::{
    Carrier, ContactFace, Coupling, HolonicInteraction, InteractionRefusal, InterfaceReading,
    Medium, MediumContact, Perspective, ReceiverBody, SourceCurrent,
};
use crate::inertia::{InertiaError, SymmetricForm};
use crate::jet_staircase::{FiniteJet, JetChart, JetLadder, StaircaseRefusal, jet_ladder};
use crate::junction_law::{
    Interface, JunctionField, JunctionRefusal, ResistiveNetwork, Side,
};
use crate::neck::{
    AnalyticWidth, ConstitutiveLink, GeometricSection, JetOrderAtNeck, LinkResidual, NeckInvariants,
    NeckReading, NeckRefusal, NeckTube, ReceiverUncertaintyWidth, TubeProfile, WidthFace,
    WidthTriple, analytic_width, check_constitutive_link, holonomy_is_identity, jet_order_at_neck,
};
use crate::rigidity_receiver::{RigidityError, RigidityJacobian};

/// The wire schema this owner's serialized values carry.
pub const HOLONIC_CHAIN_SCHEMA: &str = "holonic-engine.holonic-chain.v1";

/// **Which station of the chain is the neck.**
///
/// [definition] The five stations are the source port, the upstream medium, the neck, the
/// downstream medium and the receiver port, in that order, so the chain's neck is always its
/// third. This is *not* the same as [`TubeProfile::neck_index`], which is the tube's `argmin A_i`
/// and may fall elsewhere when a port or a medium is narrower than the coupling.
/// [`ChainTube::neck_is_narrowest`] says whether the two agree, and a disagreement is a returned
/// fact about the chain, not a defect.
pub const NECK_STATION: usize = 2;

// ===============================================================================================
// 0. ceilings and refusals
// ===============================================================================================

/// The ceiling on the number of rational probe points one rank reading takes.
pub const PROBE_CEILING: usize = 256;

/// The ceiling on the Markov order one staircase reading takes. Below
/// [`crate::jet_staircase::JET_ORDER_CEILING`], because each step is a dense exact matrix product.
pub const MARKOV_ORDER_CEILING: usize = 64;

/// The ceiling on the number of candidate cuts a hinge search scans.
pub const CUT_CEILING: usize = 1024;

/// The joint extent above which the resolvent is not inverted and the reading is returned
/// undecided within its bound rather than attempted. An exact rational inverse is cubic in the
/// extent with unbounded coefficient growth; this is the declared place that growth stops.
pub const RESOLVENT_EXTENT_CEILING: usize = 96;

/// The joint extent above which the pole atlas — a Faddeev–LeVerrier recurrence over exact
/// rationals — is not taken and the analytic width is returned undecided within its bound.
pub const ANALYTIC_EXTENT_CEILING: usize = 24;

/// The ceiling on the arithmetic work of one chain assembly, `extent²`.
pub const CHAIN_ASSEMBLY_CEILING: usize = 1 << 26;

/// Every way this module declines to answer. A refusal is a return; nothing here panics.
#[derive(Debug, Error)]
pub enum ChainRefusal {
    /// A declared size exceeded its ceiling. Nothing was allocated.
    #[error("{what} declares {declared}, above the ceiling {ceiling}")]
    DeclarationAboveCeiling {
        what: &'static str,
        declared: usize,
        ceiling: usize,
    },
    /// A product of declared sizes overflowed before it could be compared with its ceiling.
    #[error("the declared work for {what} overflows")]
    WorkOverflows { what: &'static str },
    /// The interaction does not present two media, so it is not a chain between consecutive media.
    #[error(
        "a chain is one interaction with exactly two media; this one declares {declared}, so the \
         object still owed is the multi-neck chain, whose owner would compose \
         `holonic_chain.rs::HolonicChain` over `holonic_interaction.rs::HolonicInteraction`"
    )]
    NotTwoMedia { declared: usize },
    /// `|source⟩` is not incident on a medium, so there is no upstream medium.
    #[error("a chain's source must be incident on a medium; this one is incident on {carrier}")]
    SourceIsNotOnAMedium { carrier: String },
    /// `⟨perspective|` does not read the downstream medium.
    #[error(
        "a chain's perspective must read the medium the source does not excite, or participate \
         with its own body; this one reads {chart}"
    )]
    PerspectiveIsNotDownstream { chart: String },
    /// A declared contact joins carriers that are not consecutive stations of this chain.
    #[error("the contact `{contact}` joins {left} and {right}, which are not consecutive stations")]
    ContactIsNotAStation {
        contact: String,
        left: String,
        right: String,
    },
    /// A declared state or input has the wrong extent.
    #[error("{what}: declared {declared}, found {found}")]
    WidthDisagrees {
        what: &'static str,
        declared: usize,
        found: usize,
    },
    /// A probe point sits on a pole, so the resolvent there does not exist.
    #[error("the probe `{probe}` sits on a pole of the chain: `sI − A` is singular there")]
    ProbeOnAPole { probe: String },
    /// The neck's rank bound was violated by an exact computation. The nullity theorem forbids it
    /// at every probe off the joint poles, so this is a defect in the arithmetic, not a rounding
    /// difference, and it is refused by name.
    #[error(
        "at the probe `{probe}` the transfer has rank {observed}, above the neck's rank {bound}; \
         complementary blocks of a matrix and its inverse have equal nullity, so this cannot happen"
    )]
    RankBoundViolated {
        probe: String,
        observed: usize,
        bound: usize,
    },
    /// A reading was asked for above the declared extent at which it stops.
    #[error("{what} is not decided within its bound: extent {extent} above the ceiling {ceiling}")]
    NotDecidedWithinBound {
        what: &'static str,
        extent: usize,
        ceiling: usize,
    },
    /// A cut was asked for that does not split the site population into two nonempty domains.
    #[error("the cut at site {cut} does not split {sites} sites into two nonempty domains")]
    CutIsNotAPartition { cut: usize, sites: usize },
    /// The Jacobian's configuration carries no sites, or no dimension.
    #[error("{what} is empty, and a reading over nothing is not a reading")]
    EmptyDeclaration { what: &'static str },
    #[error(transparent)]
    Interaction(#[from] InteractionRefusal),
    #[error(transparent)]
    Neck(#[from] NeckRefusal),
    #[error(transparent)]
    Staircase(#[from] StaircaseRefusal),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Inertia(#[from] InertiaError),
    #[error(transparent)]
    Junction(#[from] JunctionRefusal),
    #[error(transparent)]
    Chord(#[from] ChordRefusal),
    #[error(transparent)]
    Rigidity(#[from] RigidityError),
}

fn bounded(what: &'static str, declared: usize, ceiling: usize) -> Result<(), ChainRefusal> {
    if declared > ceiling {
        return Err(ChainRefusal::DeclarationAboveCeiling {
            what,
            declared,
            ceiling,
        });
    }
    Ok(())
}

fn bounded_square(what: &'static str, extent: usize) -> Result<(), ChainRefusal> {
    bounded_product(what, extent, extent)
}

fn bounded_product(what: &'static str, left: usize, right: usize) -> Result<(), ChainRefusal> {
    let work = left
        .checked_mul(right)
        .ok_or(ChainRefusal::WorkOverflows { what })?;
    bounded(what, work, CHAIN_ASSEMBLY_CEILING)
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn count(value: usize) -> Rat {
    Rat::from_integer(BigInt::from(value as u64))
}

/// `⟨left, right⟩` over exact rationals, refusing a length disagreement by name.
fn pairing(left: &[Rat], right: &[Rat]) -> Result<Rat, ChainRefusal> {
    if left.len() != right.len() {
        return Err(ChainRefusal::WidthDisagrees {
            what: "a pairing's two sides",
            declared: left.len(),
            found: right.len(),
        });
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| sum + a * b))
}

// ===============================================================================================
// 1. the chain
// ===============================================================================================

/// **One Holonic Interaction read as a chain: source, upstream medium, neck, downstream medium,
/// perspective.**
///
/// [definition] This is not a new unit. It is a *reading contract* over an existing
/// [`HolonicInteraction`]: the constructor checks that the unit really is a chain — two media, the
/// source on one of them, the perspective on the other or on its own body — and every method below
/// computes from that unit's declared data. No value enters this type that did not pass
/// [`HolonicInteraction::declared`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HolonicChain {
    schema: String,
    lineage: String,
    interaction: HolonicInteraction,
    upstream: Carrier,
    downstream: Carrier,
}

impl HolonicChain {
    /// Read an interaction as a chain, or refuse by name.
    ///
    /// The upstream medium is the one `|source⟩` excites; the downstream medium is the other. The
    /// perspective must read the downstream medium or participate with its own body, because a
    /// perspective that reads the upstream medium is not downstream of the neck and the rank bound
    /// would be a statement about a different object.
    pub fn over(
        lineage: impl Into<String>,
        interaction: HolonicInteraction,
    ) -> Result<Self, ChainRefusal> {
        if interaction.media().len() != 2 {
            return Err(ChainRefusal::NotTwoMedia {
                declared: interaction.media().len(),
            });
        }
        let upstream = match interaction.source().carrier() {
            Carrier::Medium(at) => Carrier::Medium(at),
            Carrier::Perspective => {
                return Err(ChainRefusal::SourceIsNotOnAMedium {
                    carrier: "the perspective's own body".to_owned(),
                });
            }
        };
        let downstream = match upstream {
            Carrier::Medium(0) => Carrier::Medium(1),
            Carrier::Medium(_) => Carrier::Medium(0),
            Carrier::Perspective => unreachable!("the upstream carrier is a medium by the match"),
        };
        let perspective = interaction.perspective();
        let reads_downstream = match perspective.carrier() {
            Some(Carrier::Perspective) => perspective.participates(),
            Some(carrier) => carrier == downstream,
            None => false,
        };
        if !reads_downstream {
            return Err(ChainRefusal::PerspectiveIsNotDownstream {
                chart: format!("{:?}", perspective.chart()),
            });
        }
        for contact in interaction.contacts() {
            let joins_media = contact.joins(upstream, downstream);
            let joins_receiver = contact.joins(downstream, Carrier::Perspective);
            if !joins_media && !joins_receiver {
                return Err(ChainRefusal::ContactIsNotAStation {
                    contact: contact.lineage().to_owned(),
                    left: format!("{:?}", contact.left()),
                    right: format!("{:?}", contact.right()),
                });
            }
        }
        // A coupling that jumps the neck — from the upstream medium straight to the receiver —
        // would make the station accounting below a partition of the wrong complex, and the
        // chain's power balance would not be this chain's. It is refused by the same name.
        for coupling in interaction.couplings() {
            let media = (coupling.from() == upstream && coupling.to() == downstream)
                || (coupling.from() == downstream && coupling.to() == upstream);
            let receiver = (coupling.from() == downstream
                && coupling.to() == Carrier::Perspective)
                || (coupling.from() == Carrier::Perspective && coupling.to() == downstream);
            if !media && !receiver {
                return Err(ChainRefusal::ContactIsNotAStation {
                    contact: coupling.lineage().to_owned(),
                    left: format!("{:?}", coupling.from()),
                    right: format!("{:?}", coupling.to()),
                });
            }
        }
        bounded_square("a chain's joint assembly", interaction.joint_dimension())?;
        Ok(Self {
            schema: HOLONIC_CHAIN_SCHEMA.to_owned(),
            lineage: lineage.into(),
            interaction,
            upstream,
            downstream,
        })
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The interaction this chain reads, whole.
    pub fn interaction(&self) -> &HolonicInteraction {
        &self.interaction
    }

    /// The medium `|source⟩` excites.
    pub fn upstream(&self) -> Carrier {
        self.upstream
    }

    /// The medium `⟨perspective|` reads across the neck.
    pub fn downstream(&self) -> Carrier {
        self.downstream
    }

    /// Whether the receiver's own coordinates join the state.
    pub fn receiver_participates(&self) -> bool {
        self.interaction.perspective().participates()
    }

    /// The block of a joint matrix cut out by two carriers.
    fn block_of(
        &self,
        matrix: &ExactRatMatrix,
        rows: Carrier,
        columns: Carrier,
    ) -> Result<ExactRatMatrix, ChainRefusal> {
        let row_offset = self.interaction.block_offset(rows)?;
        let row_extent = self.interaction.block_extent(rows)?;
        let column_offset = self.interaction.block_offset(columns)?;
        let column_extent = self.interaction.block_extent(columns)?;
        let mut carved = vec![vec![Rat::zero(); column_extent]; row_extent];
        for row in 0..row_extent {
            for column in 0..column_extent {
                carved[row][column] = matrix
                    .get(row_offset + row, column_offset + column)?
                    .clone();
            }
        }
        Ok(ExactRatMatrix::shaped(row_extent, column_extent, carved)?)
    }

    /// The coordinates of one block of the joint chart, as a slice of a joint vector.
    fn slice_of(&self, vector: &[Rat], carrier: Carrier) -> Result<Vec<Rat>, ChainRefusal> {
        let offset = self.interaction.block_offset(carrier)?;
        let extent = self.interaction.block_extent(carrier)?;
        if vector.len() < offset + extent {
            return Err(ChainRefusal::WidthDisagrees {
                what: "a joint vector against the chart it is read on",
                declared: offset + extent,
                found: vector.len(),
            });
        }
        Ok(vector[offset..offset + extent].to_vec())
    }

    /// **`A₂₁`, the neck**: the generator's `(downstream, upstream)` block.
    pub fn cross_block(&self) -> Result<ExactRatMatrix, ChainRefusal> {
        let generator = self.interaction.generator()?;
        self.block_of(&generator, self.downstream, self.upstream)
    }

    /// **The neck's coupling reading**: its rank, its exact rank factorization, and the two
    /// constituents — the skew structure's cross block and the contact form's — kept apart.
    pub fn neck_coupling(&self) -> Result<NeckCoupling, ChainRefusal> {
        let generator = self.interaction.generator()?;
        let structure = self.interaction.joint_structure()?;
        let dissipation = self.interaction.joint_dissipation()?.matrix()?;
        let storage = form_matrix(&self.interaction.joint_storage()?)?;
        let cross = self.block_of(&generator, self.downstream, self.upstream)?;
        let factorization = cross.rank_factorization()?;
        let structure_cross = self.block_of(&structure, self.downstream, self.upstream)?;
        let dissipation_cross = self.block_of(&dissipation, self.upstream, self.downstream)?;
        let conservative = structure_cross.subtract(&dissipation_cross.transpose()?)?;
        let upstream_storage = self.block_of(&storage, self.upstream, self.upstream)?;
        Ok(NeckCoupling {
            lineage: format!("{}|neck-coupling", self.lineage),
            rank: factorization.derived_rank,
            left: factorization.left,
            right: factorization.right,
            cross,
            interconnection_rank: conservative.rank()?,
            structure_cross,
            dissipation_cross,
            upstream_storage_rank: upstream_storage.rank()?,
        })
    }

    /// `H(s) = C (sI − A)⁻¹ B` at one exact rational probe.
    pub fn transfer_at(&self, probe: &Rat) -> Result<ExactRatMatrix, ChainRefusal> {
        let extent = self.interaction.joint_dimension();
        if extent > RESOLVENT_EXTENT_CEILING {
            return Err(ChainRefusal::NotDecidedWithinBound {
                what: "a chain's resolvent",
                extent,
                ceiling: RESOLVENT_EXTENT_CEILING,
            });
        }
        let generator = self.interaction.generator()?;
        let shifted = ExactRatMatrix::identity(extent)?
            .scaled(probe)
            .subtract(&generator)?;
        let resolvent = shifted
            .inverse()
            .map_err(|_| ChainRefusal::ProbeOnAPole {
                probe: probe.to_string(),
            })?;
        let readout = self.interaction.readout()?;
        let excitation = self.interaction.excitation()?;
        Ok(readout.multiply(&resolvent)?.multiply(&excitation)?)
    }

    /// **The rank bound at the neck, measured.** Every declared probe's exact transfer rank is
    /// computed and compared against the coupling's rank; a violation is refused by name.
    ///
    /// [proved-derived; formal-checked] Where the downstream block `N₂₂ = sI − A₂₂` is itself
    /// invertible, `HolonicChain.lean::transfer_rank_le_neck_rank` proves the bound; that
    /// hypothesis is separate from the joint resolvent existing and this function does not test
    /// it. [proved-standard] At every probe off the joint poles the bound still holds, by the
    /// Fiedler–Markham nullity theorem: complementary blocks of a nonsingular matrix and of its
    /// inverse have equal nullity, so `rank X₂₁ = rank N₂₁ = rank A₂₁` exactly, and
    /// `rank(C₂ X₂₁ B₁) ≤ r`. The Lean lift of that unconditional form is owed; a probe at an
    /// eigenvalue of the isolated downstream medium is covered by the standard theorem only.
    pub fn rank_bound(&self, probes: &[Rat]) -> Result<RankBoundReading, ChainRefusal> {
        if probes.is_empty() {
            return Err(ChainRefusal::EmptyDeclaration {
                what: "a rank reading's probe population",
            });
        }
        bounded("a rank reading's probe population", probes.len(), PROBE_CEILING)?;
        let coupling = self.neck_coupling()?;
        let bound = coupling.rank;
        let mut measured = Vec::with_capacity(probes.len());
        for probe in probes {
            let transfer = self.transfer_at(probe)?;
            let observed = transfer.rank()?;
            if observed > bound {
                return Err(ChainRefusal::RankBoundViolated {
                    probe: probe.to_string(),
                    observed,
                    bound,
                });
            }
            measured.push((probe.clone(), observed));
        }
        let attained = measured.iter().map(|(_, rank)| *rank).max().unwrap_or(0);
        Ok(RankBoundReading {
            lineage: format!("{}|rank-bound", self.lineage),
            bound,
            measured,
            attained,
        })
    }

    /// **The five-station power current, and the residual of the whole balance.**
    ///
    /// `state` is a joint motion `x` and `input` a source port vector `u`. Every number below is
    /// computed from the interaction's own blocks and from
    /// [`crate::holonic_interaction::ContactDissipation::power_by_face`]; nothing is declared.
    pub fn power_stations(
        &self,
        state: &[Rat],
        input: &[Rat],
    ) -> Result<PowerStations, ChainRefusal> {
        let extent = self.interaction.joint_dimension();
        if state.len() != extent {
            return Err(ChainRefusal::WidthDisagrees {
                what: "a declared state against the joint chart",
                declared: extent,
                found: state.len(),
            });
        }
        let ports = self.interaction.source().ports().len();
        if input.len() != ports {
            return Err(ChainRefusal::WidthDisagrees {
                what: "a declared input against the source's ports",
                declared: ports,
                found: input.len(),
            });
        }
        let generator = self.interaction.generator()?;
        let excitation = self.interaction.excitation()?;
        let storage = form_matrix(&self.interaction.joint_storage()?)?;
        let dissipation = self.interaction.joint_dissipation()?;
        let dissipation_matrix = dissipation.matrix()?;

        // The co-motion `G x`, at which every power in this reading is read.
        let co_motion = storage.apply(state)?;
        let drift = generator.apply(state)?;
        let forcing = excitation.apply(input)?;
        let flow: Vec<Rat> = drift
            .iter()
            .zip(&forcing)
            .map(|(left, right)| left + right)
            .collect();

        let injected = pairing(&co_motion, &forcing)?;
        let face_power = dissipation.power_by_face(&co_motion)?;
        let dissipated = face_power
            .iter()
            .fold(Rat::zero(), |sum, (_, power)| sum + power);

        // Per-block storage rate and per-block dissipation. The two together partition the whole
        // balance, which is what the transport residual checks.
        let mut blocks = vec![self.upstream, self.downstream];
        if self.receiver_participates() {
            blocks.push(Carrier::Perspective);
        }
        let mut block_storage_rate = Vec::with_capacity(blocks.len());
        let mut block_dissipation = BTreeMap::new();
        for carrier in &blocks {
            let co = self.slice_of(&co_motion, *carrier)?;
            let rate = pairing(&co, &self.slice_of(&flow, *carrier)?)?;
            let own = self.block_of(&dissipation_matrix, *carrier, *carrier)?;
            let block_power = pairing(&co, &own.apply(&co)?)?;
            block_storage_rate.push((carrier_name(*carrier), rate));
            block_dissipation.insert(carrier_name(*carrier), block_power);
        }
        let storage_rate_total = block_storage_rate
            .iter()
            .fold(Rat::zero(), |sum, (_, rate)| sum + rate);

        // The coupling powers, read directly off the generator's off-diagonal blocks.
        let co_up = self.slice_of(&co_motion, self.upstream)?;
        let co_down = self.slice_of(&co_motion, self.downstream)?;
        let state_up = self.slice_of(state, self.upstream)?;
        let state_down = self.slice_of(state, self.downstream)?;
        let leaving_upstream = -pairing(
            &co_up,
            &self
                .block_of(&generator, self.upstream, self.downstream)?
                .apply(&state_down)?,
        )?;
        let entering_downstream = pairing(
            &co_down,
            &self
                .block_of(&generator, self.downstream, self.upstream)?
                .apply(&state_up)?,
        )?;
        let cross_dissipation = pairing(
            &co_up,
            &self
                .block_of(&dissipation_matrix, self.upstream, self.downstream)?
                .apply(&co_down)?,
        )?;
        let neck_jump = integer(-2) * &cross_dissipation;

        // The receiver leg.
        let (leaving_downstream, delivered, receiver_jump) = if self.receiver_participates() {
            let co_receiver = self.slice_of(&co_motion, Carrier::Perspective)?;
            let state_receiver = self.slice_of(state, Carrier::Perspective)?;
            let leaving = -pairing(
                &co_down,
                &self
                    .block_of(&generator, self.downstream, Carrier::Perspective)?
                    .apply(&state_receiver)?,
            )?;
            let receiver_rate = block_storage_rate
                .iter()
                .find(|(name, _)| name == &carrier_name(Carrier::Perspective))
                .map(|(_, rate)| rate.clone())
                .unwrap_or_else(Rat::zero);
            let receiver_block_power = block_dissipation
                .get(&carrier_name(Carrier::Perspective))
                .cloned()
                .unwrap_or_else(Rat::zero);
            let cross = pairing(
                &co_down,
                &self
                    .block_of(&dissipation_matrix, self.downstream, Carrier::Perspective)?
                    .apply(&co_receiver)?,
            )?;
            (
                leaving,
                receiver_rate + receiver_block_power,
                integer(-2) * &cross,
            )
        } else {
            (Rat::zero(), Rat::zero(), Rat::zero())
        };

        let flux = vec![
            injected.clone(),
            leaving_upstream,
            entering_downstream,
            leaving_downstream,
            delivered.clone(),
        ];
        let upstream_sink = -(block_storage_rate[0].1.clone()
            + block_dissipation[&carrier_name(self.upstream)].clone());
        let downstream_sink = -(block_storage_rate[1].1.clone()
            + block_dissipation[&carrier_name(self.downstream)].clone());
        let source = vec![
            upstream_sink,
            neck_jump.clone(),
            downstream_sink,
            receiver_jump,
        ];

        // The wall loss per gap: the nonnegative face powers attributed to the gap whose stations
        // they sit between. Face order is `joint_faces`': the media's own faces in declaration
        // order, then the contacts in declaration order.
        let wall_loss = self.wall_loss_by_gap(&face_power)?;

        let transport_residual =
            injected.clone() - &storage_rate_total - &dissipated;
        // An arithmetic-path check, not a check of the derivation: `⟨Gx, Ax⟩ = ½xᵀ(AᵀG + GA)x`
        // holds for ANY square `A` and symmetric `G`, so this residual compares the block/vector
        // route with `causal_chord::rate_form`'s matrix route over the same `A` and `G`. Whether
        // that `A` IS the port-Hamiltonian generator is `rate_form_agrees` (`AᵀG + GA = −2GMG`).
        let rate_reading = self.interaction.storage_rate()?;
        let rate_at = rate_reading.rate_at(state)?;
        let rate_form_residual =
            (storage_rate_total.clone() - &injected) - &(rate_at / integer(2));

        Ok(PowerStations {
            lineage: format!("{}|power-stations", self.lineage),
            flux,
            source,
            wall_loss,
            face_power,
            block_storage_rate,
            injected,
            delivered,
            dissipated,
            storage_rate_total,
            neck_jump,
            cross_dissipation,
            transport_residual,
            rate_form_residual,
            rate_form_agrees: rate_reading.agrees(),
        })
    }

    /// Attribute every declared face's power to the gap it sits in. The face order is
    /// [`HolonicInteraction::joint_faces`]': every medium's own faces in declaration order, then
    /// every contact in declaration order.
    fn wall_loss_by_gap(&self, face_power: &[(String, Rat)]) -> Result<Vec<Rat>, ChainRefusal> {
        let mut gaps = vec![Rat::zero(); 4];
        let mut at = 0usize;
        let take = |at: &mut usize| -> Result<Rat, ChainRefusal> {
            let (_, power) = face_power
                .get(*at)
                .ok_or(ChainRefusal::WidthDisagrees {
                    what: "the face-power population against the declared faces",
                    declared: *at + 1,
                    found: face_power.len(),
                })?;
            *at += 1;
            Ok(power.clone())
        };
        for (index, medium) in self.interaction.media().iter().enumerate() {
            let gap = if Carrier::Medium(index) == self.upstream {
                0
            } else {
                2
            };
            for _ in 0..medium.faces().len() {
                gaps[gap] = gaps[gap].clone() + take(&mut at)?;
            }
        }
        for contact in self.interaction.contacts() {
            let gap = if contact.joins(self.upstream, self.downstream) {
                1
            } else {
                3
            };
            gaps[gap] = gaps[gap].clone() + take(&mut at)?;
        }
        Ok(gaps)
    }

    /// **The chain's five sections, computed.** `rank B`, `rank G_up`, `rank A₂₁`, `rank G_down`,
    /// `rank C`: the rank of the map the signal factors through at each station.
    pub fn sections(&self) -> Result<Vec<usize>, ChainRefusal> {
        let storage = form_matrix(&self.interaction.joint_storage()?)?;
        Ok(vec![
            self.interaction.excitation()?.rank()?,
            self.block_of(&storage, self.upstream, self.upstream)?.rank()?,
            self.neck_coupling()?.rank,
            self.block_of(&storage, self.downstream, self.downstream)?
                .rank()?,
            self.interaction.readout()?.rank()?,
        ])
    }

    /// **The chain's tube profile**: B's [`TubeProfile`] over the five stations, with sections
    /// computed by [`Self::sections`] and the current density `j_i = Φ_i / A_i` set so that the
    /// profile's own flux law returns the power current. A zero section carries `j = 0`, so the
    /// profile's flux there is zero; when the computed power current is not, the discrepancy is
    /// returned by [`ChainTube::closed_station_discrepancy`] rather than hidden.
    pub fn tube_profile(&self, stations: &PowerStations) -> Result<ChainTube, ChainRefusal> {
        let sections = self.sections()?;
        let mut declared = Vec::with_capacity(sections.len());
        let mut density = Vec::with_capacity(sections.len());
        let mut discrepancy = Vec::new();
        for (at, section) in sections.iter().enumerate() {
            let area = count(*section);
            declared.push(GeometricSection::declare(area.clone(), "channels")?);
            if area.is_zero() {
                density.push(Rat::zero());
                if !stations.flux[at].is_zero() {
                    discrepancy.push((at, stations.flux[at].clone()));
                }
            } else {
                density.push(&stations.flux[at] / &area);
            }
        }
        let profile = TubeProfile::declare(
            format!("{}|chain-tube", self.lineage),
            (0..sections.len()).map(|at| count(at)).collect(),
            declared,
            density,
            stations.source.clone(),
        )?;
        Ok(ChainTube {
            profile,
            sections,
            closed_station_discrepancy: discrepancy,
        })
    }

    /// The chain's tube as B's [`NeckTube`], with the per-gap wall loss taken from the face
    /// powers. A lossless chain's holonomy around the neck is the identity; a dissipative one's is
    /// a circuit defect.
    pub fn neck_tube(&self, stations: &PowerStations) -> Result<NeckTube, ChainRefusal> {
        let tube = self.tube_profile(stations)?;
        Ok(NeckTube::declare(tube.profile, stations.wall_loss.clone())?)
    }

    /// **The holonomy of the circuit that runs to the chain's neck and back**, through
    /// `continuing_tube`'s own checker — the same reading
    /// [`NeckTube::holonomy_around_the_neck`] takes, at the chain's declared neck station
    /// ([`NECK_STATION`]) rather than at the tube's `argmin`, which a narrow port can move.
    ///
    /// `Some(true)` is the identity — nothing dissipates between the source port and the neck's
    /// upstream side. `Some(false)` is a circuit defect. `None` means the circuit itself was
    /// refused, and no verdict is invented for it.
    ///
    /// [definition] This is a **local** reading, and which side of the interface a contact face's
    /// loss is attributed to is a bookkeeping convention — this owner puts it on the gap upstream
    /// of the station it sits at. [`Self::chain_holonomy`] is the reading that does not depend on
    /// that convention, and it is the one the reversal comparison uses.
    pub fn neck_holonomy(&self, stations: &PowerStations) -> Result<Option<bool>, ChainRefusal> {
        Ok(circuit_holonomy(&self.neck_tube(stations)?, NECK_STATION))
    }

    /// **The holonomy of the circuit that runs the whole chain and back.** It crosses every gap in
    /// both directions, so it subtracts twice the total wall loss and is independent of which side
    /// of a station a face's loss was attributed to. The identity is a lossless chain; a circuit
    /// defect is the chain's irreversibility read as tube holonomy, and it survives reversal.
    pub fn chain_holonomy(&self, stations: &PowerStations) -> Result<Option<bool>, ChainRefusal> {
        let tube = self.neck_tube(stations)?;
        let last = tube.profile().station_count() - 1;
        Ok(circuit_holonomy(&tube, last))
    }

    /// **The Markov parameters `C Aᵏ B`, exact.**
    pub fn markov(&self, order: usize) -> Result<Vec<ExactRatMatrix>, ChainRefusal> {
        bounded("a Markov reading's order", order, MARKOV_ORDER_CEILING)?;
        let extent = self.interaction.joint_dimension();
        bounded_square("a Markov reading's joint assembly", extent)?;
        let generator = self.interaction.generator()?;
        let readout = self.interaction.readout()?;
        let excitation = self.interaction.excitation()?;
        let mut power = ExactRatMatrix::identity(extent)?;
        let mut parameters = Vec::with_capacity(order + 1);
        for step in 0..=order {
            if step > 0 {
                power = power.multiply(&generator)?;
            }
            parameters.push(readout.multiply(&power)?.multiply(&excitation)?);
        }
        Ok(parameters)
    }

    /// **The chain's Markov staircase**: its impulse-response jet, the ladder that jet sits on,
    /// the relative degree, and the neck's jet order read by B's own owner.
    ///
    /// The scalar jet is taken at the declared `(receiver port, source port)` pair; the relative
    /// degree is read off the whole matrix sequence, so it does not depend on that choice.
    pub fn markov_staircase(
        &self,
        order: usize,
        receiver_port: usize,
        source_port: usize,
    ) -> Result<MarkovStaircase, ChainRefusal> {
        let parameters = self.markov(order)?;
        let mut relative_degree = None;
        for (step, parameter) in parameters.iter().enumerate() {
            if parameter.entries().iter().any(|entry| !entry.is_zero()) {
                relative_degree = Some(step);
                break;
            }
        }
        let mut coefficients = Vec::with_capacity(parameters.len());
        let mut factorial = Rat::one();
        for (step, parameter) in parameters.iter().enumerate() {
            if step > 0 {
                factorial = &factorial * &count(step);
            }
            if receiver_port >= parameter.rows() || source_port >= parameter.columns() {
                return Err(ChainRefusal::WidthDisagrees {
                    what: "a declared port pair against the Markov parameter's shape",
                    declared: receiver_port.max(source_port),
                    found: parameter.rows().max(parameter.columns()),
                });
            }
            coefficients.push(parameter.get(receiver_port, source_port)?.clone() / &factorial);
        }
        let jet = FiniteJet::declare(
            JetChart::unit(format!("{}|impulse-response", self.lineage)),
            coefficients,
        )?;
        let ladder = jet_ladder(&jet)?;
        let neck_order = jet_order_at_neck(
            &jet,
            &Rat::zero(),
            format!("{}|the chain's impulse response at the neck", self.lineage),
        );
        Ok(MarkovStaircase {
            lineage: format!("{}|markov-staircase", self.lineage),
            parameters,
            jet,
            ladder,
            relative_degree,
            read_to: order,
            neck_order,
        })
    }

    /// **The telescoping residual** `(sI − A) Σ_{k<N} s^{N−1−k} Aᵏ − (s^N I − A^N)`, which the
    /// Lean owner proves is exactly zero. Computed here rather than asserted, so a defect in the
    /// exact arithmetic is a returned number.
    pub fn telescope_residual(&self, probe: &Rat, order: usize) -> Result<Rat, ChainRefusal> {
        bounded("a telescope reading's order", order, MARKOV_ORDER_CEILING)?;
        let extent = self.interaction.joint_dimension();
        bounded_square("a telescope reading's joint assembly", extent)?;
        let generator = self.interaction.generator()?;
        let identity = ExactRatMatrix::identity(extent)?;
        let mut partial = ExactRatMatrix::zero(extent, extent)?;
        let mut power = identity.clone();
        for step in 0..order {
            if step > 0 {
                power = power.multiply(&generator)?;
            }
            let weight = pow_rat(probe, order - 1 - step);
            partial = partial.add(&power.scaled(&weight))?;
        }
        let top = if order == 0 {
            identity.clone()
        } else {
            power.multiply(&generator)?
        };
        let left = identity.scaled(probe).subtract(&generator)?.multiply(&partial)?;
        let right = identity.scaled(&pow_rat(probe, order)).subtract(&top)?;
        let difference = left.subtract(&right)?;
        Ok(difference
            .entries()
            .iter()
            .fold(Rat::zero(), |sum, entry| sum + entry.abs()))
    }

    /// **The chain's three widths and the declared link between two of them.**
    ///
    /// The geometric section is the neck's; the analytic width is
    /// [`crate::neck::analytic_width`] over this chain's own pole atlas; the receiver width is
    /// whatever the caller has already read through
    /// [`crate::neck::neck_two_axis_width`], which is that owner's and is not recomputed here.
    /// They meet only through the declared [`ConstitutiveLink`], whose residual is returned.
    pub fn chain_widths(
        &self,
        stations: &PowerStations,
        receiver: Option<ReceiverUncertaintyWidth>,
        link: ConstitutiveLink,
    ) -> Result<ChainWidths, ChainRefusal> {
        let tube = self.tube_profile(stations)?;
        // The neck's geometric section is `rank A₂₁` at the chain's own neck station, not the
        // tube's narrowest section: a one-port source is narrow without being a neck.
        let geometric = tube.profile.sections()[NECK_STATION].clone();
        let extent = self.interaction.joint_dimension();
        let (analytic, scope) = if extent > ANALYTIC_EXTENT_CEILING {
            (
                None,
                AnalyticScope::NotDecidedWithinBound {
                    extent,
                    ceiling: ANALYTIC_EXTENT_CEILING,
                },
            )
        } else {
            let atlas = self.poles(PoleReading::Named)?;
            (Some(analytic_width(&atlas)?), AnalyticScope::Taken)
        };
        let triple = WidthTriple {
            geometric,
            receiver,
            analytic,
        };
        let residual = check_constitutive_link(&link, &triple);
        Ok(ChainWidths {
            lineage: format!("{}|chain-widths", self.lineage),
            triple,
            link,
            residual,
            scope,
        })
    }

    /// The chain's pole atlas, through the interaction's own reading, bounded before it is taken.
    pub fn poles(&self, reading: PoleReading) -> Result<PoleAtlas, ChainRefusal> {
        let extent = self.interaction.joint_dimension();
        if extent > ANALYTIC_EXTENT_CEILING {
            return Err(ChainRefusal::NotDecidedWithinBound {
                what: "a chain's pole atlas",
                extent,
                ceiling: ANALYTIC_EXTENT_CEILING,
            });
        }
        Ok(self.interaction.poles(reading)?)
    }

    /// **Every neck invariant of this chain, assembled over one source**, in B's own
    /// [`NeckInvariants`]. Absent invariants stay `None` and are named by
    /// [`NeckInvariants::open_invariants`]; nothing is defaulted.
    pub fn neck_invariants(
        &self,
        stations: &PowerStations,
        widths: &ChainWidths,
        staircase: &MarkovStaircase,
    ) -> Result<NeckInvariants, ChainRefusal> {
        let _ = self.tube_profile(stations)?;
        let station = NECK_STATION;
        let holonomy = self.neck_holonomy(stations)?;
        let mut domains = BTreeMap::new();
        domains.insert(
            "geometric section".to_owned(),
            "the rank of the map the chain factors through at that station".to_owned(),
        );
        domains.insert(
            "jet order".to_owned(),
            "the chain's impulse-response jet at the declared port pair".to_owned(),
        );
        if widths.triple.analytic.is_some() {
            domains.insert(
                "analytic width".to_owned(),
                "the pole atlas of this chain's own transfer denominator".to_owned(),
            );
        }
        if widths.triple.receiver.is_some() {
            domains.insert(
                "receiver uncertainty width".to_owned(),
                "the two-axis horizon the caller declared".to_owned(),
            );
        }
        if holonomy.is_some() {
            domains.insert(
                "holonomy".to_owned(),
                "the flux face carried around the neck of this chain's own tube".to_owned(),
            );
        }
        Ok(NeckInvariants {
            lineage: format!("{}|neck-invariants", self.lineage),
            station,
            widths: widths.triple.clone(),
            holonomy_is_identity: holonomy,
            linking: None,
            growth: None,
            jet_order: staircase.neck_order.clone(),
            domains,
        })
    }

    /// **The interface condition at the neck**, through A's own [`InterfaceReading`].
    ///
    /// The complex is the physical one: a control node for each side of the neck and a joint node
    /// at the interface, with the two power currents as the field and the neck's own sink as the
    /// source on the joint. `check_junction`'s divergence at a node is inflow minus outflow, so
    /// the source entered there is `Φ₁ − Φ₂`, which is the jump negated once into that owner's
    /// orientation — the same single sign `neck.rs` documents.
    pub fn interface_reading(
        &self,
        stations: &PowerStations,
    ) -> Result<InterfaceReading, ChainRefusal> {
        let network = ResistiveNetwork::declare(
            format!("{}|neck-interface", self.lineage),
            3,
            &[(0usize, 1usize, Rat::one()), (1usize, 2usize, Rat::one())],
        )?;
        let operator = network.operator();
        let field = vec![stations.flux[1].clone(), stations.flux[2].clone()];
        let mut source = vec![Rat::zero(); operator.extent(0)];
        source[0] = -stations.flux[1].clone();
        source[1] = &stations.flux[1] - &stations.flux[2];
        source[2] = stations.flux[2].clone();
        let sides = operator
            .cells(1)
            .iter()
            .enumerate()
            .map(|(at, cell)| (*cell, if at == 0 { Side::Left } else { Side::Right }))
            .collect();
        let joint: BTreeSet<CausalCellId> = BTreeSet::from([operator.cells(0)[1]]);
        let interface = Interface::declare(
            format!("{}|neck-joint", self.lineage),
            operator,
            0,
            sides,
            joint,
        )?;
        let potential = vec![Rat::zero(); operator.extent(0)];
        Ok(InterfaceReading::read(
            format!("{}|interface", self.lineage),
            self.upstream,
            self.downstream,
            operator,
            &interface,
            &JunctionField {
                potential: &potential,
                field: &field,
                source: &source,
            },
            network.units(),
        )?)
    }

    /// **The chain with every skew structure reversed**: `Ω ↦ −Ω` on each medium, on the receiver's
    /// body and on each coupling. The faces — and therefore `M` — are untouched, which is the
    /// point.
    pub fn reversed(&self) -> Result<Self, ChainRefusal> {
        let media = self
            .interaction
            .media()
            .iter()
            .map(|medium| {
                Medium::declared(
                    format!("{}|reversed", medium.lineage()),
                    medium.storage().clone(),
                    medium.structure().scaled(&integer(-1)),
                    medium.faces().to_vec(),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let couplings = self
            .interaction
            .couplings()
            .iter()
            .map(|coupling| {
                Coupling::declared(
                    format!("{}|reversed", coupling.lineage()),
                    coupling.from(),
                    coupling.to(),
                    coupling.block().scaled(&integer(-1)),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let perspective = match self.interaction.perspective().body() {
            Some(body) => Perspective::participating(
                format!("{}|reversed", self.interaction.perspective().lineage()),
                self.interaction.perspective().aperture().clone(),
                self.interaction.perspective().ports().to_vec(),
                ReceiverBody::declared(
                    format!("{}|reversed", body.lineage()),
                    body.storage().clone(),
                    body.structure().scaled(&integer(-1)),
                )?,
            )?,
            None => self.interaction.perspective().clone(),
        };
        let interaction = HolonicInteraction::declared(
            format!("{}|reversed", self.interaction.lineage()),
            self.interaction.source().clone(),
            media,
            self.interaction.contacts().to_vec(),
            couplings,
            None,
            perspective,
        )?;
        Self::over(format!("{}|reversed", self.lineage), interaction)
    }

    /// **What reversal preserves and what it does not.**
    ///
    /// The *adjoint* chain — source and perspective exchanged, generator transposed — has transfer
    /// `H(s)ᵀ` exactly, which is reciprocity, so its rank at every probe is the same. The
    /// *structure-reversed* chain has the same contact faces and therefore the same dissipated
    /// power at the same co-motion: reversal does not undo dissipation. Both are computed.
    pub fn reversal_reading(
        &self,
        probes: &[Rat],
        state: &[Rat],
        input: &[Rat],
    ) -> Result<ReversalReading, ChainRefusal> {
        let forward = self.rank_bound(probes)?;
        let mut reciprocal = true;
        for probe in probes {
            let transfer = self.transfer_at(probe)?;
            let adjoint = self.adjoint_transfer_at(probe)?;
            if adjoint != transfer.transpose()? {
                reciprocal = false;
            }
        }
        let reversed = self.reversed()?;
        let forward_power = self.power_stations(state, input)?;
        let reversed_power = reversed.power_stations(state, input)?;
        let reversed_rank = reversed.rank_bound(probes)?;
        let forward_tube = self.neck_tube(&forward_power)?;
        let reversed_profile = forward_tube.profile().reversed()?;
        let reversed_tube = NeckTube::declare(
            reversed_profile,
            forward_power.wall_loss.iter().rev().cloned().collect(),
        )?;
        let last = forward_tube.profile().station_count() - 1;
        let forward_holonomy = circuit_holonomy(&forward_tube, last);
        let reversed_holonomy = circuit_holonomy(&reversed_tube, last);
        Ok(ReversalReading {
            lineage: format!("{}|reversal", self.lineage),
            forward_rank: forward.bound,
            reversed_rank: reversed_rank.bound,
            rank_is_symmetric: forward.bound == reversed_rank.bound,
            reciprocal,
            forward_dissipated: forward_power.dissipated.clone(),
            reversed_dissipated: reversed_power.dissipated.clone(),
            dissipation_is_even: forward_power.dissipated == reversed_power.dissipated,
            forward_flux: forward_power.flux.clone(),
            reversed_flux: forward_tube
                .profile()
                .fluxes()
                .iter()
                .rev()
                .map(|flux| -flux.clone())
                .collect(),
            forward_holonomy_is_identity: forward_holonomy,
            reversed_holonomy_is_identity: reversed_holonomy,
        })
    }

    /// `Bᵀ (sI − Aᵀ)⁻¹ Cᵀ`, the adjoint chain's transfer.
    pub fn adjoint_transfer_at(&self, probe: &Rat) -> Result<ExactRatMatrix, ChainRefusal> {
        let extent = self.interaction.joint_dimension();
        if extent > RESOLVENT_EXTENT_CEILING {
            return Err(ChainRefusal::NotDecidedWithinBound {
                what: "a chain's adjoint resolvent",
                extent,
                ceiling: RESOLVENT_EXTENT_CEILING,
            });
        }
        let generator = self.interaction.generator()?.transpose()?;
        let shifted = ExactRatMatrix::identity(extent)?
            .scaled(probe)
            .subtract(&generator)?;
        let resolvent = shifted
            .inverse()
            .map_err(|_| ChainRefusal::ProbeOnAPole {
                probe: probe.to_string(),
            })?;
        let readout = self.interaction.excitation()?.transpose()?;
        let excitation = self.interaction.readout()?.transpose()?;
        Ok(readout.multiply(&resolvent)?.multiply(&excitation)?)
    }

    /// **The typed reading at the tube's narrowest station**, from B's own owner, at a declared
    /// receiver grain: `Open`, `Pinhole` or `Closed`.
    ///
    /// [definition] B's reading is taken at `argmin A_i`, which is [`NECK_STATION`] exactly when
    /// [`ChainTube::neck_is_narrowest`]. When a one-port source or a thin medium is narrower than
    /// the coupling the reading is about that station instead, and the caller is told which by
    /// [`NeckReading::station`].
    ///
    /// [implemented-exact] "Plural inside" is computed, not declared: the interior plurality is
    /// the smaller computed section beside the station read — for the structural neck,
    /// `min(rank G_up, rank G_down)`, the modes the media carry into and out of the `r` channels.
    /// A pinhole whose interior plurality is one is a single-mode chain, and the reading says so.
    pub fn neck_reading(
        &self,
        stations: &PowerStations,
        grain: &Rat,
    ) -> Result<NeckReading, ChainRefusal> {
        let tube = self.tube_profile(stations)?;
        let at = tube.profile.neck_index();
        let before = at.checked_sub(1).and_then(|index| tube.sections.get(index));
        let after = tube.sections.get(at + 1);
        let beside = match (before, after) {
            (Some(left), Some(right)) => *left.min(right),
            (Some(only), None) | (None, Some(only)) => *only,
            (None, None) => 0,
        };
        let interior_plurality = Rat::from_integer(BigInt::from(beside));
        Ok(tube.profile.neck_reading(grain, &interior_plurality))
    }
}

/// The circuit `station 0 → turn → station 0`, through `continuing_tube`'s own checker. This is
/// the call [`NeckTube::holonomy_around_the_neck`] makes, at a declared turning station instead of
/// at the profile's `argmin`, which a one-port source can move.
fn circuit_holonomy(tube: &NeckTube, turn: usize) -> Option<bool> {
    check_circuit_holonomy(
        tube,
        &[0usize, turn, 0usize],
        &[0usize],
        &[(0usize, Rat::one())],
    )
    .ok()
    .map(|verdict| holonomy_is_identity(&verdict))
}

fn carrier_name(carrier: Carrier) -> String {
    match carrier {
        Carrier::Medium(at) => format!("medium[{at}]"),
        Carrier::Perspective => "perspective".to_owned(),
    }
}

fn form_matrix(form: &SymmetricForm) -> Result<ExactRatMatrix, ChainRefusal> {
    let extent = form.extent();
    let rows = (0..extent)
        .map(|row| (0..extent).map(|column| form.at(row, column).clone()).collect())
        .collect();
    Ok(ExactRatMatrix::shaped(extent, extent, rows)?)
}

fn pow_rat(base: &Rat, exponent: usize) -> Rat {
    let mut value = Rat::one();
    for _ in 0..exponent {
        value = &value * base;
    }
    value
}

// ===============================================================================================
// 2. the readings
// ===============================================================================================

/// **The neck's coupling, with its rank and its exact factorization.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NeckCoupling {
    lineage: String,
    rank: usize,
    left: ExactRatMatrix,
    right: ExactRatMatrix,
    cross: ExactRatMatrix,
    interconnection_rank: usize,
    structure_cross: ExactRatMatrix,
    dissipation_cross: ExactRatMatrix,
    upstream_storage_rank: usize,
}

impl NeckCoupling {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// **`r`: the neck's geometric section.** The rank of `A₂₁ = (Ω₂₁ − M₂₁) G₁`.
    pub fn rank(&self) -> usize {
        self.rank
    }

    /// `U` of `A₂₁ = U V`, the `r` channels as they leave the upstream medium.
    pub fn left(&self) -> &ExactRatMatrix {
        &self.left
    }

    /// `V` of `A₂₁ = U V`, the `r` coordinate functionals the downstream medium reads.
    pub fn right(&self) -> &ExactRatMatrix {
        &self.right
    }

    /// `A₂₁` itself.
    pub fn cross(&self) -> &ExactRatMatrix {
        &self.cross
    }

    /// The rank of `Ω₂₁ − M₂₁` alone, **before** the upstream storage form acts. It is an upper
    /// bound for [`Self::rank`] and is kept apart from it so the two are never confused.
    pub fn interconnection_rank(&self) -> usize {
        self.interconnection_rank
    }

    /// `Ω₂₁`, the skew interconnection's cross block.
    pub fn structure_cross(&self) -> &ExactRatMatrix {
        &self.structure_cross
    }

    /// `M₁₂`, the contact form's cross block, in upstream rows and downstream columns.
    pub fn dissipation_cross(&self) -> &ExactRatMatrix {
        &self.dissipation_cross
    }

    /// `rank G₁`, which bounds the neck's rank from the upstream side.
    pub fn upstream_storage_rank(&self) -> usize {
        self.upstream_storage_rank
    }

    /// **The pinhole**: a single channel at the interface's grain.
    pub fn is_pinhole(&self) -> bool {
        self.rank == 1
    }

    /// **Closed**: the two media do not communicate, so the chain transmits exactly nothing.
    pub fn is_closed(&self) -> bool {
        self.rank == 0
    }

    /// Whether the coupling carries a dissipative part at all.
    pub fn is_dissipative(&self) -> bool {
        self.dissipation_cross
            .entries()
            .iter()
            .any(|entry| !entry.is_zero())
    }
}

/// What the measured rank bound returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RankBoundReading {
    lineage: String,
    bound: usize,
    measured: Vec<(Rat, usize)>,
    attained: usize,
}

impl RankBoundReading {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// `r`, the neck's rank: the bound the factorization proves.
    pub fn bound(&self) -> usize {
        self.bound
    }

    /// Every declared probe and the exact rank of the transfer there.
    pub fn measured(&self) -> &[(Rat, usize)] {
        &self.measured
    }

    /// The largest rank any probe attained. Equal to the bound when the bound is sharp at some
    /// probe, and smaller when the declared probes did not reach it — which is a statement about
    /// the probes, not about the chain.
    pub fn attained(&self) -> usize {
        self.attained
    }

    /// Whether some declared probe attained the bound.
    pub fn bound_is_attained(&self) -> bool {
        self.attained == self.bound
    }
}

/// **The five-station power current of one chain at one declared state and input.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PowerStations {
    lineage: String,
    flux: Vec<Rat>,
    source: Vec<Rat>,
    wall_loss: Vec<Rat>,
    face_power: Vec<(String, Rat)>,
    block_storage_rate: Vec<(String, Rat)>,
    injected: Rat,
    delivered: Rat,
    dissipated: Rat,
    storage_rate_total: Rat,
    neck_jump: Rat,
    cross_dissipation: Rat,
    transport_residual: Rat,
    rate_form_residual: Rat,
    rate_form_agrees: bool,
}

impl PowerStations {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// `Φ₀ … Φ₄`: the power current at the source port, leaving the upstream medium, entering the
    /// downstream medium, leaving the downstream medium and delivered to the receiver.
    pub fn flux(&self) -> &[Rat] {
        &self.flux
    }

    /// `σ₀ … σ₃`: the net power injected into each gap, computed from the block storage rates and
    /// the block and cross dissipation — never from the fluxes.
    pub fn source(&self) -> &[Rat] {
        &self.source
    }

    /// The nonnegative dissipated power in each gap, which is the tube's wall loss.
    pub fn wall_loss(&self) -> &[Rat] {
        &self.wall_loss
    }

    /// Every declared face's dissipated power, as A's own owner returned it.
    pub fn face_power(&self) -> &[(String, Rat)] {
        &self.face_power
    }

    /// Each block's storage rate, by name.
    pub fn block_storage_rate(&self) -> &[(String, Rat)] {
        &self.block_storage_rate
    }

    /// `⟨u, Bᵀ G x⟩`.
    pub fn injected(&self) -> &Rat {
        &self.injected
    }

    /// The power delivered to the receiver's own block, or zero for a standing perspective.
    pub fn delivered(&self) -> &Rat {
        &self.delivered
    }

    /// `⟨Gx, M Gx⟩`, summed over the declared faces.
    pub fn dissipated(&self) -> &Rat {
        &self.dissipated
    }

    /// `d/dt (½⟨x, Gx⟩)`, summed over the blocks.
    pub fn storage_rate_total(&self) -> &Rat {
        &self.storage_rate_total
    }

    /// `Φ₂ − Φ₁ = −2⟨(Gx)_up, M_c (Gx)_down⟩`: the jump in the power current across the neck.
    pub fn neck_jump(&self) -> &Rat {
        &self.neck_jump
    }

    /// `⟨(Gx)_up, M_c (Gx)_down⟩`, the cross term itself.
    pub fn cross_dissipation(&self) -> &Rat {
        &self.cross_dissipation
    }

    /// **`injected − Σ storage − Σ dissipation`.** Exactly zero when the block and face population
    /// really is a partition of the balance; returned as an exact rational, never rounded.
    pub fn transport_residual(&self) -> &Rat {
        &self.transport_residual
    }

    /// `(Σ storage − injected) − ½ xᵀ(AᵀG + GA)x`: the block/vector route against
    /// [`crate::causal_chord::rate_form`]'s matrix route. It is an identity for any `A` and
    /// symmetric `G`, so it checks the arithmetic paths only; the derivation `AᵀG + GA = −2GMG`
    /// is checked by [`PowerStations::rate_form_agrees`].
    pub fn rate_form_residual(&self) -> &Rat {
        &self.rate_form_residual
    }

    /// Whether A's own storage-rate reading found `AᵀG + GA = −2GMG` entry by entry.
    pub fn rate_form_agrees(&self) -> bool {
        self.rate_form_agrees
    }

    /// Whether the power current is continuous across the neck: true exactly when the coupling
    /// carries no cross dissipation at this co-motion.
    pub fn neck_is_lossless(&self) -> bool {
        self.neck_jump.is_zero()
    }

    /// Whether every gap balances: `Φ_{i+1} − Φ_i − σ_i = 0` at each one.
    pub fn balances(&self) -> bool {
        (0..self.source.len())
            .all(|gap| (&self.flux[gap + 1] - &self.flux[gap]) - &self.source[gap] == Rat::zero())
    }
}

/// The chain's tube: B's profile, the computed sections, and any station whose section closed
/// while the power current there did not vanish.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainTube {
    profile: TubeProfile,
    sections: Vec<usize>,
    closed_station_discrepancy: Vec<(usize, Rat)>,
}

impl ChainTube {
    /// B's own profile, whole.
    pub fn profile(&self) -> &TubeProfile {
        &self.profile
    }

    /// The computed section at each station.
    pub fn sections(&self) -> &[usize] {
        &self.sections
    }

    /// Stations whose section is zero while the computed power current there is not. A closed
    /// station forces the profile's flux to zero; this is what that forcing discarded, returned
    /// rather than hidden.
    pub fn closed_station_discrepancy(&self) -> &[(usize, Rat)] {
        &self.closed_station_discrepancy
    }

    /// `argmin A_i`, from B's own owner: the tube's narrowest station.
    pub fn narrowest_station(&self) -> usize {
        self.profile.neck_index()
    }

    /// Whether the chain's neck really is the tube's narrowest station. When it is not, a port or
    /// a medium is narrower than the coupling, and that is a fact about the chain — a one-port
    /// source is a pinhole of its own — not a defect of the reading.
    pub fn neck_is_narrowest(&self) -> bool {
        self.profile.neck_index() == NECK_STATION
    }
}

/// **The chain's Markov staircase.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarkovStaircase {
    lineage: String,
    parameters: Vec<ExactRatMatrix>,
    jet: FiniteJet,
    ladder: JetLadder,
    relative_degree: Option<usize>,
    read_to: usize,
    neck_order: JetOrderAtNeck,
}

impl MarkovStaircase {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// `C Aᵏ B` for `k = 0 … read_to`.
    pub fn parameters(&self) -> &[ExactRatMatrix] {
        &self.parameters
    }

    /// The impulse response's jet at the declared port pair, in the unit chart.
    pub fn jet(&self) -> &FiniteJet {
        &self.jet
    }

    /// The ladder that jet sits on, from `jet_staircase`'s own owner.
    pub fn ladder(&self) -> &JetLadder {
        &self.ladder
    }

    /// **The relative degree**: the least `k` with `C Aᵏ B ≠ 0`. `None` means *not decided within
    /// the declared order* — a finite prefix of the staircase proves nothing beyond itself.
    pub fn relative_degree(&self) -> Option<usize> {
        self.relative_degree
    }

    /// The order the staircase was read to, so a `None` degree is bounded rather than bare.
    pub fn read_to(&self) -> usize {
        self.read_to
    }

    /// The neck's jet order, from B's own [`jet_order_at_neck`].
    pub fn neck_order(&self) -> &JetOrderAtNeck {
        &self.neck_order
    }

    /// Whether the chain has no direct feedthrough, which the Lean owner proves for every chain
    /// whose ports are separated.
    pub fn has_no_direct_feedthrough(&self) -> bool {
        self.parameters
            .first()
            .is_some_and(|parameter| parameter.entries().iter().all(Zero::is_zero))
    }
}

/// Whether the analytic width was taken, or left undecided within its declared bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum AnalyticScope {
    /// The pole atlas was taken and the width is present.
    Taken,
    /// The joint extent exceeded the ceiling at which this owner stops; no width was invented.
    NotDecidedWithinBound { extent: usize, ceiling: usize },
}

/// The chain's three widths, each still in its own type, with the declared link's residual.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainWidths {
    lineage: String,
    triple: WidthTriple,
    link: ConstitutiveLink,
    residual: Option<LinkResidual>,
    scope: AnalyticScope,
}

impl ChainWidths {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn triple(&self) -> &WidthTriple {
        &self.triple
    }

    /// The geometric section at the neck.
    pub fn geometric(&self) -> &GeometricSection {
        &self.triple.geometric
    }

    /// The analytic width, when the atlas was within its bound.
    pub fn analytic(&self) -> Option<&AnalyticWidth> {
        self.triple.analytic.as_ref()
    }

    /// The receiver's uncertainty width, when one was handed in.
    pub fn receiver(&self) -> Option<&ReceiverUncertaintyWidth> {
        self.triple.receiver.as_ref()
    }

    /// The declared link between two of the three faces.
    pub fn link(&self) -> &ConstitutiveLink {
        &self.link
    }

    /// `observed − coefficient · from` over the link's declared domain, or `None` when the triple
    /// does not carry one of the two faces.
    pub fn residual(&self) -> Option<&LinkResidual> {
        self.residual.as_ref()
    }

    pub fn scope(&self) -> AnalyticScope {
        self.scope
    }

    /// Which faces of the link the triple could not supply.
    pub fn absent_faces(&self) -> Vec<WidthFace> {
        let mut absent = Vec::new();
        for face in [self.link.from(), self.link.to()] {
            let present = match face {
                WidthFace::Geometric => true,
                WidthFace::Analytic => self.triple.analytic.is_some(),
                WidthFace::ReceiverUncertainty => self.triple.receiver.is_some(),
            };
            if !present {
                absent.push(face);
            }
        }
        absent
    }
}

/// **What reversing the chain preserves and what it does not.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReversalReading {
    lineage: String,
    forward_rank: usize,
    reversed_rank: usize,
    rank_is_symmetric: bool,
    reciprocal: bool,
    forward_dissipated: Rat,
    reversed_dissipated: Rat,
    dissipation_is_even: bool,
    forward_flux: Vec<Rat>,
    reversed_flux: Vec<Rat>,
    forward_holonomy_is_identity: Option<bool>,
    reversed_holonomy_is_identity: Option<bool>,
}

impl ReversalReading {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn forward_rank(&self) -> usize {
        self.forward_rank
    }

    pub fn reversed_rank(&self) -> usize {
        self.reversed_rank
    }

    /// Whether the **structure-reversed** chain's neck rank equals the forward one. This is a
    /// computed comparison of two different generators, not the reciprocity statement: a coupling
    /// that mixes a skew part with a dissipative one need not give the same rank both ways, and
    /// when it does not, that is a fact about the chain. The reversal-symmetry the Lean owner
    /// proves is [`Self::reciprocal`].
    pub fn rank_is_symmetric(&self) -> bool {
        self.rank_is_symmetric
    }

    /// **Reciprocity.** The adjoint chain's transfer is the transpose of this one's, at every
    /// declared probe.
    pub fn reciprocal(&self) -> bool {
        self.reciprocal
    }

    pub fn forward_dissipated(&self) -> &Rat {
        &self.forward_dissipated
    }

    pub fn reversed_dissipated(&self) -> &Rat {
        &self.reversed_dissipated
    }

    /// **Even under reversal, and this is the point.** Running the chain the other way dissipates
    /// exactly as much: reversal acts on the skew structure and leaves the contact form alone.
    pub fn dissipation_is_even(&self) -> bool {
        self.dissipation_is_even
    }

    /// The forward power current.
    pub fn forward_flux(&self) -> &[Rat] {
        &self.forward_flux
    }

    /// **Odd under reversal.** The tube's own flux reverses and changes sign, because flux through
    /// an oriented face is signed.
    pub fn reversed_flux(&self) -> &[Rat] {
        &self.reversed_flux
    }

    /// The whole-chain circuit's holonomy, forward.
    pub fn forward_holonomy_is_identity(&self) -> Option<bool> {
        self.forward_holonomy_is_identity
    }

    /// The whole-chain circuit's holonomy after `TubeProfile::reversed`. A dissipative chain's
    /// defect survives the reversal: that is the irreversibility, exactly.
    pub fn reversed_holonomy_is_identity(&self) -> Option<bool> {
        self.reversed_holonomy_is_identity
    }
}

// ===============================================================================================
// 3. the consumer: a protein hinge is a neck between two media
// ===============================================================================================

/// **The cross-domain stiffness block of one declared cut, and its rank.**
///
/// [definition] With `A = −JᵀJ`, `Ω = 0` and `G = I`, the generator's `(downstream, upstream)`
/// block is `−J_downᵀ J_up`. Only constraints whose two sites straddle the cut contribute, so the
/// section is at most the number of crossing constraints — and is computed, not bounded by hand.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CutSection {
    /// The number of sites in the upstream domain.
    pub cut: usize,
    /// `rank A₂₁`: the neck's geometric section at this cut.
    pub section: usize,
    /// How many declared constraints straddle the cut.
    pub crossing_constraints: usize,
    /// How many constraints live inside the upstream domain.
    pub upstream_constraints: usize,
    /// How many live inside the downstream domain.
    pub downstream_constraints: usize,
}

/// What a bounded scan over candidate cuts concluded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum HingeVerdict {
    /// Every cut admitted by the declared margin was scanned, so the minimum is the minimum over
    /// that scope — which the margin names and which is not every cut of the structure unless the
    /// margin is one.
    Minimal { cut: usize, section: usize },
    /// The scan stopped at its declared bound. The minimum returned is the minimum **over the
    /// prefix scanned**, and a finite prefix proves nothing about the rest.
    NotDecidedWithinBound {
        cut: usize,
        section: usize,
        scanned: usize,
        sites: usize,
    },
}

/// **A bounded search for the hinge: the cut whose neck section is smallest.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HingeSearch {
    lineage: String,
    margin: usize,
    scanned: Vec<CutSection>,
    verdict: HingeVerdict,
    ties: Vec<usize>,
}

impl HingeSearch {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared margin: the least number of sites a domain must carry to count as a domain.
    /// A margin of `1` admits the terminal cuts, where a single site faces the rest of the chain.
    /// [agent-inferred] from the measured RBX1 section profiles: those cuts are usually the
    /// narrowest and are usually not hinges.
    pub fn margin(&self) -> usize {
        self.margin
    }

    /// Every candidate cut that was scanned, with its section.
    pub fn scanned(&self) -> &[CutSection] {
        &self.scanned
    }

    /// The verdict, which names its own scope.
    pub fn verdict(&self) -> &HingeVerdict {
        &self.verdict
    }

    /// The cut the search settled on.
    pub fn cut(&self) -> usize {
        match self.verdict {
            HingeVerdict::Minimal { cut, .. }
            | HingeVerdict::NotDecidedWithinBound { cut, .. } => cut,
        }
    }

    /// Its section.
    pub fn section(&self) -> usize {
        match self.verdict {
            HingeVerdict::Minimal { section, .. }
            | HingeVerdict::NotDecidedWithinBound { section, .. } => section,
        }
    }

    /// Every other cut attaining the same section. A hinge that is not unique is a fact about the
    /// structure, not a failure of the search.
    pub fn ties(&self) -> &[usize] {
        &self.ties
    }
}

/// The cross-domain stiffness block `−J_downᵀ J_up` of one declared cut.
pub fn cross_stiffness(
    jacobian: &RigidityJacobian,
    cut: usize,
) -> Result<ExactRatMatrix, ChainRefusal> {
    let dimension = jacobian.dimension();
    let sites = jacobian.occurrence_count();
    if dimension == 0 || sites == 0 {
        return Err(ChainRefusal::EmptyDeclaration {
            what: "a rigidity Jacobian's configuration",
        });
    }
    if cut == 0 || cut >= sites {
        return Err(ChainRefusal::CutIsNotAPartition { cut, sites });
    }
    let split = dimension
        .checked_mul(cut)
        .ok_or(ChainRefusal::WorkOverflows { what: "a cut" })?;
    let width = dimension
        .checked_mul(sites)
        .ok_or(ChainRefusal::WorkOverflows { what: "a chart" })?;
    bounded_square("a cut's cross block", width)?;
    let rows = jacobian.matrix.rows();
    bounded(
        "a cut's constraint population",
        rows,
        crate::holonic_interaction::DECLARED_FACE_CEILING,
    )?;
    bounded_product("a cut's constraint assembly", rows, width)?;
    let mut upper = vec![vec![Rat::zero(); split]; rows];
    let mut lower = vec![vec![Rat::zero(); width - split]; rows];
    for row in 0..rows {
        for column in 0..split {
            upper[row][column] = jacobian.matrix.get(row, column)?.clone();
        }
        for column in split..width {
            lower[row][column - split] = jacobian.matrix.get(row, column)?.clone();
        }
    }
    let upstream = ExactRatMatrix::shaped(rows, split, upper)?;
    let downstream = ExactRatMatrix::shaped(rows, width - split, lower)?;
    Ok(downstream
        .transpose()?
        .multiply(&upstream)?
        .scaled(&integer(-1)))
}

/// **The section of one declared cut**, with the constraint population that produced it.
pub fn cut_section(jacobian: &RigidityJacobian, cut: usize) -> Result<CutSection, ChainRefusal> {
    let cross = cross_stiffness(jacobian, cut)?;
    let mut crossing = 0usize;
    let mut upstream = 0usize;
    let mut downstream = 0usize;
    for constraint in &jacobian.constraints {
        let lower_up = constraint.lower_block < cut;
        let upper_up = constraint.upper_block < cut;
        match (lower_up, upper_up) {
            (true, true) => upstream += 1,
            (false, false) => downstream += 1,
            _ => crossing += 1,
        }
    }
    Ok(CutSection {
        cut,
        section: cross.rank()?,
        crossing_constraints: crossing,
        upstream_constraints: upstream,
        downstream_constraints: downstream,
    })
}

/// **Find the hinge by computation: the cut whose neck section is minimal, within a declared
/// margin and a declared bound.**
///
/// The scan runs over `cut = margin … sites − margin`, truncated at `bound` candidates. The
/// **margin** is the least number of sites a domain must carry to be a domain: at `margin = 1` the
/// terminal cuts are admitted. [agent-inferred] from the measured section profiles (section 2 of 8
/// and 3 of 15 at the ends of the RBX1 windows): a terminal cut is usually the narrowest simply
/// because one residue has few neighbours — narrow without being a hinge. When the bound truncates the scan
/// the verdict says so and names both numbers, because a finite prefix never proves a universal
/// claim.
pub fn hinge_by_minimal_section(
    jacobian: &RigidityJacobian,
    margin: usize,
    bound: usize,
) -> Result<HingeSearch, ChainRefusal> {
    let sites = jacobian.occurrence_count();
    if margin == 0 || sites < 2 * margin {
        return Err(ChainRefusal::CutIsNotAPartition { cut: margin, sites });
    }
    bounded("a hinge search's candidate population", bound, CUT_CEILING)?;
    let admissible = sites - 2 * margin + 1;
    let candidates = admissible.min(bound);
    if candidates == 0 {
        return Err(ChainRefusal::EmptyDeclaration {
            what: "a hinge search's candidate population",
        });
    }
    let mut scanned = Vec::with_capacity(candidates);
    for cut in margin..margin + candidates {
        scanned.push(cut_section(jacobian, cut)?);
    }
    let best = scanned
        .iter()
        .min_by_key(|candidate| (candidate.section, candidate.cut))
        .expect("the candidate population is nonempty");
    let ties = scanned
        .iter()
        .filter(|candidate| candidate.section == best.section && candidate.cut != best.cut)
        .map(|candidate| candidate.cut)
        .collect();
    let verdict = if candidates == admissible {
        HingeVerdict::Minimal {
            cut: best.cut,
            section: best.section,
        }
    } else {
        HingeVerdict::NotDecidedWithinBound {
            cut: best.cut,
            section: best.section,
            scanned: candidates,
            sites,
        }
    };
    Ok(HingeSearch {
        lineage: format!("{}|hinge-search", jacobian.presentation_lineage),
        margin,
        scanned,
        verdict,
        ties,
    })
}

/// **Build the chain of an elastic network cut into two domains.**
///
/// `Ω = 0`, `G = I`, `M = JᵀJ`: every rigidity constraint row **is** a contact face, with slip map
/// that row and unit response, so the faces are derived from the measured constraints rather than
/// declared. Constraints inside a domain are that medium's faces; constraints crossing the cut are
/// the neck. The source excites every upstream coordinate and the perspective reads every
/// downstream one, so the rank bound at the neck is a statement about the whole cross-domain
/// transfer and not about one chosen port.
pub fn elastic_chain(
    lineage: impl Into<String>,
    jacobian: &RigidityJacobian,
    cut: usize,
) -> Result<HolonicChain, ChainRefusal> {
    let lineage = lineage.into();
    let dimension = jacobian.dimension();
    let sites = jacobian.occurrence_count();
    if dimension == 0 || sites == 0 {
        return Err(ChainRefusal::EmptyDeclaration {
            what: "a rigidity Jacobian's configuration",
        });
    }
    if cut == 0 || cut >= sites {
        return Err(ChainRefusal::CutIsNotAPartition { cut, sites });
    }
    let split = dimension
        .checked_mul(cut)
        .ok_or(ChainRefusal::WorkOverflows { what: "a cut" })?;
    let width = dimension
        .checked_mul(sites)
        .ok_or(ChainRefusal::WorkOverflows { what: "a chart" })?;
    bounded_square("an elastic chain's joint assembly", width)?;
    bounded(
        "an elastic chain's constraint population",
        jacobian.constraints.len(),
        crate::holonic_interaction::DECLARED_FACE_CEILING,
    )?;
    bounded_product(
        "an elastic chain's constraint assembly",
        jacobian.constraints.len(),
        width,
    )?;
    let response = SymmetricForm::from_rows(vec![vec![Rat::one()]])?;

    let mut upstream_faces = Vec::new();
    let mut downstream_faces = Vec::new();
    let mut crossing_faces = Vec::new();
    for (at, constraint) in jacobian.constraints.iter().enumerate() {
        let row: Vec<Rat> = (0..width)
            .map(|column| jacobian.matrix.get(at, column).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let lower_up = constraint.lower_block < cut;
        let upper_up = constraint.upper_block < cut;
        match (lower_up, upper_up) {
            (true, true) => {
                let slip = ExactRatMatrix::shaped(1, split, vec![row[..split].to_vec()])?;
                upstream_faces.push(ContactFace::declared(
                    format!("{lineage}|upstream-constraint[{at}]"),
                    slip,
                    response.clone(),
                    Rat::one(),
                )?);
            }
            (false, false) => {
                let slip =
                    ExactRatMatrix::shaped(1, width - split, vec![row[split..].to_vec()])?;
                downstream_faces.push(ContactFace::declared(
                    format!("{lineage}|downstream-constraint[{at}]"),
                    slip,
                    response.clone(),
                    Rat::one(),
                )?);
            }
            _ => {
                let slip = ExactRatMatrix::shaped(1, width, vec![row])?;
                crossing_faces.push(MediumContact::declared(
                    format!("{lineage}|neck-constraint[{at}]"),
                    Carrier::Medium(0),
                    Carrier::Medium(1),
                    ContactFace::declared(
                        format!("{lineage}|neck-constraint[{at}]|face"),
                        slip,
                        response.clone(),
                        Rat::one(),
                    )?,
                )?);
            }
        }
    }

    let upstream = Medium::declared(
        format!("{lineage}|upstream"),
        identity_form(split)?,
        ExactRatMatrix::zero(split, split)?,
        upstream_faces,
    )?;
    let downstream = Medium::declared(
        format!("{lineage}|downstream"),
        identity_form(width - split)?,
        ExactRatMatrix::zero(width - split, width - split)?,
        downstream_faces,
    )?;
    let source = SourceCurrent::declared(
        format!("{lineage}|source"),
        Carrier::Medium(0),
        ExactRatMatrix::identity(split)?,
        (0..split).map(|at| format!("upstream-site-coordinate[{at}]")).collect(),
    )?;
    let perspective = Perspective::standing(
        format!("{lineage}|perspective"),
        Carrier::Medium(1),
        ExactRatMatrix::identity(width - split)?,
        (0..width - split)
            .map(|at| format!("downstream-site-coordinate[{at}]"))
            .collect(),
    )?;
    let interaction = HolonicInteraction::declared(
        format!("{lineage}|interaction"),
        source,
        vec![upstream, downstream],
        crossing_faces,
        Vec::new(),
        None,
        perspective,
    )?;
    HolonicChain::over(lineage, interaction)
}

fn identity_form(extent: usize) -> Result<SymmetricForm, ChainRefusal> {
    let rows = (0..extent)
        .map(|row| {
            (0..extent)
                .map(|column| if row == column { Rat::one() } else { Rat::zero() })
                .collect()
        })
        .collect();
    Ok(SymmetricForm::from_rows(rows)?)
}

#[cfg(test)]
mod tests;
