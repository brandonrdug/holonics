//! Production on the oriented incidence complex: the vertex, not the tape.
//!
//! The production path this is built beside walks a suffix ecology over token sequences. In
//! diagram terms that is a chain of propagators with **no vertex** — a free line — and
//! `research/records/2026-08-11_THE_TAPE_HAS_NO_VERTEX_AND_PRODUCTION_IS_RECEPTION_AT_THE_OTHER_HAND.md`
//! §5 states the construction that replaces it. The ratified Information Chemistry law it obeys is
//! `research/records/2026-07-19_THE_INCIDENCE_REACTS_THE_COMPOUND_EXPOSES_ITS_BOUNDARY_THE_REGION_CARRIES_THE_FIELD.md`
//! §§I–II, which convicts `bytes.windows(2)` as *"one tape chart"* that cannot stand as the
//! geometry of an event.
//!
//! ```text
//! L_t = (K_t, ∂_t, o_t, ⪯_t, Γ_t)
//! ```
//!
//! | term | owner here |
//! |---|---|
//! | `K_t` cells at each material grain | [`Site`] (dimension 0), [`Bond`] (1), [`Compound`] (2), each carrying its own `grain` |
//! | `∂_t` oriented boundary, `∂∂ = 0` | [`IncidenceComplex::event_complex`] hands the whole thing to `body::incidence::EventComplex`, whose validator *is* the `∂∂ = 0` check. No second complex is built. |
//! | `o_t` hand | `body::incidence::IncidenceHand`, carried on every incidence and on every route passage |
//! | `⪯_t` actual source dependency | [`Site::causal_rank`], the longest-path rank in the corpus's own `caused_by` relation. **Never the storage ordinal**, which is carried beside it in [`DeclaredOccurrence::storage_ordinal`] only so the two can be exhibited apart. |
//! | `Γ_t` ingress / exposed / return | [`IncidenceComplex::ingress`] / [`Emission::residual`]'s exposed sites. See the boundary note below: the body owns only two port species. |
//!
//! # The transport law, declared
//!
//! For an admitted route `γ = (v₀, e₁, v₁, …, e_k, v_k)`,
//!
//! ```text
//!   amplitude(γ)  =  ( Π_i o_γ(e_i) ) · ( T_{e_k} ∘ … ∘ T_{e_1} )  applied to  1 + 0i
//!
//!   T_e   =  R_chart(m_e) ^ σ_e          crossed along the declared hand
//!   T_e⁻¹                                 crossed against it
//! ```
//!
//! - `o_γ(e)` is `+1` when the route crosses `e` along its declared hand and `−1` against it —
//!   literally `IncidenceHand::coefficient()`, the same coefficient that makes `∂∂ = 0` telescope.
//!   `CLAUDE.md` §2b: a sign is the hand of a **passage**, and `−1 = e^{iπ}` is the half turn.
//! - `m_e` is the contact's own §III transition count, `popcount(tail(from) ⊕ head(to))` — *how
//!   far* the contact crosses. It fixes the magnitude of the turn.
//! - `σ_e` is the **sheet** the contact lands on, `(−1)^{popcount(head(to))}` — §III's
//!   *"equal adjacent bits remain on one sheet; a changed bit crosses to the opposed sheet"*. It
//!   fixes the **sense** of the turn, and it is a materially independent reading from `m_e`. That
//!   independence is what makes both falsifiers two-sided: a chart in which every generator turns
//!   the same way can never return a closed loop to the identity, so flatness would be
//!   unreachable and the curvature receipt would be a tautology (`CLAUDE.md` §8).
//! - Transport is carried on the **contact**, so reversing a loop returns the exact inverse and
//!   *flat ⟺ identity* is direction-invariant. The chain sign is **not** part of the holonomy:
//!   on an odd-length closed boundary it flips with the traversal direction, so it is a gauge of
//!   the 2-chain and is reported as one. Promoting it into the invariant would be §0's fourth
//!   lesson exactly — a receiver-visible coordinate read as an invariant.
//! - `R_chart` is one of three **declared charts** ([`PhaseChart`]). `HalfTurnOnly` switches the
//!   rotation off entirely — that is `H.0216`'s tower with the relation switched off, i.e.
//!   Pythagoras, i.e. the tape. The other two are genuinely different rational rotations. A
//!   conclusion that does not survive all three is chart-dependent and is reported as such,
//!   because `CLAUDE.md` §8 convicts a gauge whose group acts trivially on the material.
//!
//! Two routes reaching one site are superposed by
//! `holonic_engine::ExactReceiverPhasePopulation::receive`, which sums **in mode, before any
//! quadratic response is formed**. Cancellation is therefore the engine's own arithmetic and not
//! this module's; a count could not have produced it, which is the whole complaint the record
//! raised against the tape path.
//!
//! # Adjacency is `∂`, never `⪯`
//!
//! Within one occurrence, the contact between consecutive inscription patches supplies **boundary
//! incidence**. §III of the ratified law licenses this explicitly — byte serialization is a lawful
//! source chart — and what it forbids is that chart *counterfeiting* another. So adjacency founds
//! `∂` and the corpus's `caused_by` founds `⪯`, and the two are exhibited apart by
//! [`IncidenceComplex::dependency_disagrees_with_storage`].
//!
//! # Differentiation, and response to later material
//!
//! Closure runs one way: `complete_{F,Q,k}(C_k) → (n_{k+1}, ρ_k)`, a completed compound hands up
//! one successor at grain `k+1` and its internal boundary **departs**. [`IncidenceComplex::differentiate`]
//! is the formal partner, and the two are adjoint:
//!
//! ```text
//!     differentiate_k(n_{k+1}) → (∂Σ, r_Σ, supp_Σ)          ⟨w, ∂Σ⟩  =  ⟨dw, Σ⟩
//! ```
//!
//! The right-hand side is `holonic_engine::running_integral::coboundary` on the engine's own
//! carrier, reached through [`IncidenceComplex::engine_view`]; no second complex and no second
//! validator is built here. `w(e) = sheet(e) · contact_winding(e)` is the **additive** reading of
//! the same two material numbers the multiplicative transport uses, and the two are not the same
//! map — `PhaseChart::rotation` is not a homomorphism out of `(ℤ,+)` — so their agreement on
//! flatness is a measurement and never an assumption.
//!
//! [`IncidenceComplex::admit_later`] is the response. It derives the arrival's place in `⪯` from
//! the family's own `caused_by`, founds its cells, and returns an [`ArrivalResponse`] carrying the
//! before and after emissions with a [`ClosureVerdict`] per standing closed boundary. **Three
//! things are measured and they are three different questions**, which the first statement of this
//! law conflated:
//!
//! | question | predictor | measured |
//! |---|---|---|
//! | does the **closed boundary** move? | — | **never.** Adding cells to a graph cannot destroy a cycle; a closed boundary is permanent, which is what *closed* means. |
//! | does the **valence** `Γ` move? | a passage that did not exist lands on a constituent of `∂Σ` that is not already `Both` | 21 of 21 across three declared arrivals |
//! | what does the compound **hand forward**? | `r_Σ`, through `r(Σ' − Σ) = r(Σ') − r(Σ)` | exact; a saturated compound hands forward zero |
//!
//! The third is what makes the residual causal rather than reported, and it is a theorem about the
//! linearity of `⟨w, ·⟩` on the cycle space rather than a rule authored here.
//! [`IncidenceComplex::withdraw`] is the inverse of admission **on the admitted complex**, so a
//! retained multiplicity or a retained `⪯` edge shows up as a non-bit-exact restoration.
//!
//! # Boundary: the body owns two port species, the law names three
//!
//! `body::incidence::EventPortKind` is `{Ingress, Exposed}`. The ratified law's `Γ_t` names
//! *ingress, exposed boundary, and return*. This module therefore carries the return port as a
//! **polarity on an exposed site** ([`ExposedPolarity`], §IV's donor/acceptor), and does not
//! invent a third species inside the body. That is a real gap between the specification and the
//! organ, and it is reported rather than papered over.

use std::collections::{BTreeMap, BTreeSet};

use body::{
    incidence::{
        EventCell, EventCellId, EventComplex, EventComplexError, EventPort, EventPortKind,
        IncidenceHand, OrientedIncidence,
    },
    num::Cog,
};
use holonic_engine::{
    running_integral::{
        coboundary, found_potential_in, ChordObstruction, Cochain, CoefficientGroup,
    },
    CausalCellId, CausalChain, ComparativeMultiplicity, DimensionalWaveModeId, EventId,
    ExactComplexWaveCurrent, ExactReceiverPhasePopulation, ExactWavePhaseTransport,
    GradedCausalComplex,
};
use num_bigint::BigInt;
use num_rational::BigRational;

/// The exact rational carrier. Identical to `relational_geometry::Rat`, which is the same
/// `num_rational::BigRational`; no float enters this module at any point.
pub type Rat = BigRational;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IncidenceProductionError {
    /// No occurrence was declared.
    NoDeclaredMaterial,
    /// The declared family's `caused_by` relation is not a partial order over itself.
    CausalCycle,
    /// An occurrence carried no inscription patch at the declared extent.
    EmptyOccurrence(String),
    /// A declared patch carried no octets or no identity. A patch with no carrier has no boundary
    /// and cannot carry a winding, so it is not a constituent.
    EmptyPatch,
    /// No contact survived: every patch pair was a self-contact, or every occurrence was one patch.
    NoContact,
    /// The complex declared no exposed boundary, so nothing can hand up.
    NoExposedBoundary,
    /// `body::incidence` refused the complex. This is the `∂∂ = 0` verdict.
    Body(EventComplexError),
    /// A declared rotation left the exact unit conic. Unreachable through the declared charts;
    /// retained because the engine's constructor can say so and this module must not assume.
    NonUnitRotation,
    Extent,
    /// `holonic_engine::algebraic::GradedCausalComplex` refused a cell. This is its own `∂∂ = 0`
    /// verdict, taken independently of `body::incidence`'s.
    Engine(String),
    /// `holonic_engine::running_integral` refused a pairing, a coboundary or a potential search.
    Integral(String),
    /// The arrival names a cause that is not in the declared family, so its place in `⪯` cannot be
    /// derived. It is refused rather than given rank zero, which would silently make a caused
    /// occurrence a root.
    ArrivalCauseIsOutsideTheFamily(String),
    /// A declared contact-face chart did not have exactly one entry per admitted adjacent patch
    /// pair, or a face was empty. The relation is refused rather than shifted onto another bond.
    ContactFaceExtent,
}

/// One patch of inscription, as the material's own codec cut it.
///
/// **The cut is the codec's and never this organ's.** Until 2026-08-13 the organ cut every
/// occurrence with `split_whitespace()` and keyed each site on the resulting `String`, so the mouth
/// admitted exactly one material — whitespace-delimited UTF-8 compared by byte equality — and the
/// two authored decisions sat where no caller could vary them. That is the level rule
/// (`CLAUDE.md` §8: *a level is either read off the material or declared by the caller — never
/// authored inside the organ*) and it is also `33_THE_NECK.md` §1's ruling, deposited 2026-07-04:
/// *"meaning lives in the relating-web BETWEEN encapsulations, never inside one — a glyph's meaning
/// is not its bits, which is the deepest form of why text-as-byte-stream was never the
/// communication medium."*
///
/// So a patch carries two things that were previously one:
///
/// - [`Patch::octets`] — the material's **own carrier** at this position, unnormalized. Adjacency
///   between consecutive patches founds `∂`; the octets found the §III windings. For text these are
///   UTF-8 bytes, for a weight file they are the datum's own words, and nothing converts between
///   them.
/// - [`Patch::identity`] — what the codec declares makes two patches **the same patch**. Two
///   patches at one causal rank found one site exactly when their identities are equal.
///
/// For the text codec ([`DeclaredOccurrence::from_text`]) identity is the surface, which reproduces
/// the previous behaviour exactly. A codec whose material has no meaningful surface equality — a
/// weight file, a sampled signal — declares an identity that is a **transformation class**, and the
/// mouth then founds sites on recurring transformation rather than on recurring bytes.
///
/// The founding identity is the codec's; the **revision** is behavioural, and is not this type's
/// job: `crate::decomposing_codec` compresses the reading and re-cuts at the collapsed pair's own
/// separating word. Founding under conduct would be circular — the complex must exist before its
/// conduct partition does — so the codec declares, and the returned collapse revises.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Patch {
    octets: Vec<u8>,
    identity: String,
}

impl Patch {
    /// Declare a patch. Refuses an empty carrier: a patch with no octets has no boundary and could
    /// not carry a winding, so it is not a constituent.
    pub fn new(
        octets: Vec<u8>,
        identity: impl Into<String>,
    ) -> Result<Self, IncidenceProductionError> {
        let identity = identity.into();
        if octets.is_empty() || identity.is_empty() {
            return Err(IncidenceProductionError::EmptyPatch);
        }
        Ok(Self { octets, identity })
    }

    /// The material's own carrier at this patch.
    pub fn octets(&self) -> &[u8] {
        &self.octets
    }

    /// What the codec declares makes two patches the same patch.
    pub fn identity(&self) -> &str {
        &self.identity
    }
}

/// One occurrence of the declared material, as the corpus carries it.
///
/// `storage_ordinal` is present **only so that `⪯` can be shown not to be it**. Nothing in this
/// module reads it except [`IncidenceComplex::dependency_disagrees_with_storage`].
///
/// `inscription` is the codec's cut. See [`Patch`] for why the organ no longer performs it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclaredOccurrence {
    pub identity: String,
    pub storage_ordinal: u64,
    pub caused_by: BTreeSet<String>,
    pub inscription: Vec<Patch>,
}

impl DeclaredOccurrence {
    /// **The text codec, declared rather than authored.**
    ///
    /// Cuts on whitespace and takes the surface as the identity — bit-for-bit what the organ did
    /// internally before 2026-08-13. It is now one codec among possible codecs, named at the call
    /// site, and a caller that wants a different grain supplies its own patches instead.
    pub fn from_text(
        identity: impl Into<String>,
        storage_ordinal: u64,
        caused_by: BTreeSet<String>,
        text: impl AsRef<str>,
    ) -> Result<Self, IncidenceProductionError> {
        let mut inscription = Vec::new();
        for patch in text.as_ref().split_whitespace() {
            inscription.push(Patch::new(patch.as_bytes().to_vec(), patch)?);
        }
        Ok(Self {
            identity: identity.into(),
            storage_ordinal,
            caused_by,
            inscription,
        })
    }

    /// The inscription rendered as its declared patch identities, space-joined.
    ///
    /// **Exhibition only.** This is a face — it forgets the octets and the cut — and no
    /// construction may read it. It exists because a driver printing what it declared should print
    /// the codec's own names for the patches, not a re-encoding of them.
    pub fn declared_surface(&self) -> String {
        let mut surface = String::new();
        for patch in &self.inscription {
            if !surface.is_empty() {
                surface.push(' ');
            }
            surface.push_str(patch.identity());
        }
        surface
    }
}

/// One exterior face of a contact, retained as lineage through transport.
///
/// This is deliberately not a reaction class. A source atlas may call a face `operand`, `calls`,
/// or `adjacency`; a later behavioral quotient decides whether two such faces conduct alike. The
/// complex keeps the declaration only so that transport cannot erase which contact was supplied.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeclaredContactFace(String);

impl DeclaredContactFace {
    pub fn new(face: impl Into<String>) -> Result<Self, IncidenceProductionError> {
        let face = face.into();
        if face.is_empty() {
            return Err(IncidenceProductionError::ContactFaceExtent);
        }
        Ok(Self(face))
    }

    pub fn name(&self) -> &str {
        &self.0
    }

    fn inscription_adjacency() -> Self {
        Self("inscription-adjacency".to_owned())
    }
}

// ---------------------------------------------------------------------------------------------
// The cells
// ---------------------------------------------------------------------------------------------

/// A bounded constituent: one inscription patch at grain `k`, dimension 0.
///
/// It is not a token with neighbours. It has a boundary (its own two boundary octets), a hand
/// (the contact hands it participates in), and a place in `⪯` (`causal_rank`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Site {
    pub id: EventCellId,
    /// The codec's declared identity for this constituent: what made these patches one site.
    /// For the text codec this is the word, which is why every prior reading is unchanged.
    pub surface: String,
    /// The material's **own octets** at this constituent, retained unnormalized as lineage and as
    /// the carrier every §III winding is taken over. Before 2026-08-13 the windings were taken over
    /// `surface.as_bytes()`, so a non-text material's windings would have been read off a UTF-8
    /// encoding of its identity rather than off the material.
    pub octets: Vec<u8>,
    pub causal_rank: u32,
    pub grain: u32,
    /// §III: the number of adjacent bit transitions across this constituent's own octet stream.
    pub octet_winding: u32,
    /// `Π`, the lived construction: how many times this constituent occurred. It is counted and
    /// reported and it decides nothing (`CLAUDE.md` §13 rule 2).
    pub occurrences: u64,
}

/// A consequential oriented contact between two constituents: dimension 1.
///
/// `∂bond = to − from`, so `from` enters at `IncidenceHand::Against` and `to` at
/// `IncidenceHand::With`, and the two coefficients sum to zero. That sum is what
/// `body::incidence` checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bond {
    pub id: EventCellId,
    pub from: usize,
    pub to: usize,
    pub causal_rank: u32,
    pub grain: u32,
    /// The §III transition count across the contact: `popcount(tail(from) ⊕ head(to))`. How far
    /// the contact crosses, hence the magnitude of the turn it carries.
    pub contact_winding: u32,
    /// The §III sheet the contact lands on: `+1` same sheet, `−1` opposed. The sense of the turn.
    pub sheet: i8,
    pub multiplicity: u64,
    /// Complete exterior contact-face population which caused this bond. It participates in no
    /// constitutive decision; it survives so a later receiver can test, ablate, or quotient it.
    pub contact_faces: BTreeSet<DeclaredContactFace>,
}

/// A closed internal boundary: dimension 2, one element of the fundamental cycle basis.
///
/// `bonds[i]` is crossed with `hands[i]`; `sites[i]` is the constituent the crossing arrives at.
/// The traversal telescopes, so `∂compound = 0` by construction and `body::incidence` confirms it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compound {
    pub id: EventCellId,
    pub bonds: Vec<usize>,
    pub hands: Vec<IncidenceHand>,
    pub sites: Vec<usize>,
    pub causal_rank: u32,
    pub grain: u32,
    /// The non-tree contact that forced this cycle. The spanning forest condenses for free; the
    /// chords are the remainder (`CLAUDE.md` §11).
    pub chord: usize,
}

/// One upward attempt: a standing constituent reaching toward an arriving one.
///
/// **The attachment is two-sided, and this type exists because it was one-sided.** Until
/// 2026-08-13 an arrival landed on the standing complex by identity coincidence alone — its patches
/// founded constituents, and any that happened to key equal to a standing constituent at the same
/// causal rank became that constituent. The terrain contributed nothing. That is exactly the
/// picture the one ratified law in this corpus about arrival refuses,
/// `research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL_THE_RETURN_TRAVELS_THE_FOUND_PATH.md`
/// Card D, registered as `H.0466`:
///
/// > *"The continuous cloud-ground path FOUNDs at actual local contact between grown constructions;
/// > ground is not a passive terminal selected from above."*
///
/// with the requirement that *"A lightning world must admit plural upward leaders and retain
/// connected and unconnected outcomes instead of manufacturing one ground endpoint."*
///
/// So every exposed standing constituent reaches toward every arriving one, and **whether the two
/// meet is decided by both sides**: §IV's law is that donor and acceptor are *opposed* boundary
/// roles, so a pair connects exactly when their polarities are opposed and refuses when they are
/// the same. Neither side chooses the attachment point; the pair does. And the attempts that do not
/// meet are returned rather than dropped, because an unconnected upward leader is a real occurrence
/// and deleting it would manufacture the single endpoint the law forbids.
///
/// **Both polarities are read off the complex's own bonds and dependencies**, which come from the
/// material's inscription — so this classification is not the preimage of a field a driver
/// authored, and varying the material moves it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttachmentAttempt {
    /// The standing constituent that reached.
    pub terrain_site: usize,
    pub terrain_surface: String,
    pub terrain_polarity: ExposedPolarity,
    /// The arriving constituent it reached toward.
    pub arrival_site: usize,
    pub arrival_surface: String,
    pub arrival_polarity: ExposedPolarity,
    /// §III, the material's own reading of the gap: how far the contact would cross, and which
    /// sheet it would land on. Retained on every attempt, connected or not, so an unconnected one
    /// is inspectable rather than a bare refusal.
    pub contact_winding: u32,
    pub sheet: i8,
    /// Whether the two grown constructions actually met.
    pub connected: bool,
}

/// §IV: donor and acceptor are opposed boundary roles, not absolute labels.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExposedPolarity {
    /// An external contact leaves this site: the compound can donate here.
    Donor,
    /// An external contact arrives at this site: the compound can accept here.
    Acceptor,
    Both,
}

impl ExposedPolarity {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Donor => "donor",
            Self::Acceptor => "acceptor",
            Self::Both => "both",
        }
    }

    pub const fn donates(self) -> bool {
        matches!(self, Self::Donor | Self::Both)
    }

    pub const fn accepts(self) -> bool {
        matches!(self, Self::Acceptor | Self::Both)
    }
}

// ---------------------------------------------------------------------------------------------
// The declared phase charts
// ---------------------------------------------------------------------------------------------

/// A declared rational rotation chart on the material's own winding number.
///
/// Each chart is a map `w ↦ t_chart(w)` from a material integer to a rational tangent half-angle,
/// and the rotation is the exact rational point `((1−t²)/(1+t²), 2t/(1+t²))` on the unit conic.
/// `w = 0` is the identity in every chart, so a flat constituent turns nothing in any of them.
///
/// Three charts exist because one is not a frame. `CLAUDE.md` §8: *a gauge whose group acts
/// trivially on the declared material is not a gauge* — so the orbit is taken, not assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PhaseChart {
    /// `t = 0`. The rotation is switched off and the amplitude is the bare hand `±1`. This is the
    /// tower with the relation switched off — Pythagoras — and therefore the tape's own chart.
    HalfTurnOnly,
    /// `t = w / (w + 1)`.
    WindingAdjacent,
    /// `t = w / (w + 2)`.
    WindingSpread,
}

impl PhaseChart {
    pub const ALL: [Self; 3] = [
        Self::HalfTurnOnly,
        Self::WindingAdjacent,
        Self::WindingSpread,
    ];

    pub const fn name(self) -> &'static str {
        match self {
            Self::HalfTurnOnly => "half-turn-only",
            Self::WindingAdjacent => "winding-adjacent",
            Self::WindingSpread => "winding-spread",
        }
    }

    /// The declared tangent half-angle `t = numerator / denominator`.
    const fn half_angle(self, winding: u32) -> (u64, u64) {
        match self {
            Self::HalfTurnOnly => (0, 1),
            Self::WindingAdjacent => (winding as u64, winding as u64 + 1),
            Self::WindingSpread => (winding as u64, winding as u64 + 2),
        }
    }

    /// The exact rational rotation this chart assigns to a material winding number.
    pub fn rotation(
        self,
        winding: u32,
    ) -> Result<ExactWavePhaseTransport, IncidenceProductionError> {
        let (numerator, denominator) = self.half_angle(winding);
        let p = BigInt::from(numerator);
        let q = BigInt::from(denominator);
        let square_sum = &q * &q + &p * &p;
        let cosine = Rat::new(&q * &q - &p * &p, square_sum.clone());
        let sine = Rat::new(BigInt::from(2) * &p * &q, square_sum);
        ExactWavePhaseTransport::new(cosine, sine)
            .map_err(|_| IncidenceProductionError::NonUnitRotation)
    }

    /// The transport one contact carries: the chart's rotation at the contact's own crossing
    /// magnitude, turned onto the sheet the contact lands on.
    pub fn contact_transport(
        self,
        winding: u32,
        sheet: i8,
    ) -> Result<ExactWavePhaseTransport, IncidenceProductionError> {
        let rotation = self.rotation(winding)?;
        Ok(if sheet < 0 {
            rotation.inverse()
        } else {
            rotation
        })
    }
}

// ---------------------------------------------------------------------------------------------
// The complex
// ---------------------------------------------------------------------------------------------

/// One bounded source-native oriented incidence complex at one material grain.
#[derive(Clone, Debug)]
pub struct IncidenceComplex {
    grain: u32,
    sites: Vec<Site>,
    bonds: Vec<Bond>,
    compounds: Vec<Compound>,
    /// `⪯`: same constituent, later causal rank. Never a storage relation.
    dependencies: Vec<(usize, usize)>,
    ingress: Vec<usize>,
    exposed: Vec<usize>,
    ingress_was_declared: bool,
    exposed_was_declared: bool,
    patch_extent: usize,
    patches_outside_extent: u64,
    self_contacts_refused: u64,
    causal_ranks: Vec<(String, u64, u32)>,
}

impl IncidenceComplex {
    pub fn grain(&self) -> u32 {
        self.grain
    }
    pub fn sites(&self) -> &[Site] {
        &self.sites
    }
    pub fn bonds(&self) -> &[Bond] {
        &self.bonds
    }
    pub fn compounds(&self) -> &[Compound] {
        &self.compounds
    }
    pub fn dependencies(&self) -> &[(usize, usize)] {
        &self.dependencies
    }
    pub fn ingress(&self) -> &[usize] {
        &self.ingress
    }
    pub fn exposed(&self) -> &[usize] {
        &self.exposed
    }
    /// §IV's boundary role for one constituent, read off this complex's own bonds and `⪯` edges.
    ///
    /// `None` when the constituent participates in neither, which is an isolated cell and exposes
    /// no role at all. This is the same law `hand_up` applies per compound, taken globally so an
    /// arrival can be met.
    pub fn site_polarity(&self, at: usize) -> Option<ExposedPolarity> {
        let mut donates = false;
        let mut accepts = false;
        for bond in &self.bonds {
            if bond.from == at {
                donates = true;
            }
            if bond.to == at {
                accepts = true;
            }
        }
        for (before, after) in &self.dependencies {
            if *before == at {
                donates = true;
            }
            if *after == at {
                accepts = true;
            }
        }
        match (donates, accepts) {
            (true, true) => Some(ExposedPolarity::Both),
            (true, false) => Some(ExposedPolarity::Donor),
            (false, true) => Some(ExposedPolarity::Acceptor),
            (false, false) => None,
        }
    }

    /// **The two-sided attachment.** Every standing constituent that exposes a role reaches toward
    /// every constituent the arrival founded, and the pair decides whether they meet.
    ///
    /// Read on the complex *after* admission, with `trace` naming which constituents are the
    /// arrival's: anything at or beyond [`ArrivalTrace::base_sites`] was founded by it. Both
    /// outcomes are returned. See [`AttachmentAttempt`] for the law and why the unconnected ones
    /// may not be dropped.
    pub fn attachment(&self, trace: &ArrivalTrace) -> Vec<AttachmentAttempt> {
        let mut attempts = Vec::new();
        for terrain_site in 0..trace.base_sites.min(self.sites.len()) {
            let Some(terrain_polarity) = self.site_polarity(terrain_site) else {
                continue;
            };
            for arrival_site in trace.base_sites..self.sites.len() {
                let Some(arrival_polarity) = self.site_polarity(arrival_site) else {
                    continue;
                };
                let connected = match (terrain_polarity, arrival_polarity) {
                    // A constituent exposing both roles can meet either.
                    (ExposedPolarity::Both, _) | (_, ExposedPolarity::Both) => true,
                    // Opposed roles meet; equal roles have no direction between them.
                    (ExposedPolarity::Donor, ExposedPolarity::Acceptor)
                    | (ExposedPolarity::Acceptor, ExposedPolarity::Donor) => true,
                    _ => false,
                };
                attempts.push(AttachmentAttempt {
                    terrain_site,
                    terrain_surface: self.sites[terrain_site].surface.clone(),
                    terrain_polarity,
                    arrival_site,
                    arrival_surface: self.sites[arrival_site].surface.clone(),
                    arrival_polarity,
                    contact_winding: contact_winding(
                        &self.sites[terrain_site].octets,
                        &self.sites[arrival_site].octets,
                    ),
                    sheet: sheet_of(&self.sites[arrival_site].octets),
                    connected,
                });
            }
        }
        attempts
    }

    pub fn ingress_was_declared(&self) -> bool {
        self.ingress_was_declared
    }
    pub fn exposed_was_declared(&self) -> bool {
        self.exposed_was_declared
    }
    pub fn patch_extent(&self) -> usize {
        self.patch_extent
    }
    /// The outside the declared aperture returned: patches present in the material and not admitted.
    pub fn patches_outside_extent(&self) -> u64 {
        self.patches_outside_extent
    }
    /// At grain 0, contacts a constituent made with itself and which were refused. Above grain 0,
    /// [`Self::next_grain`] stores the **incoherently glued** pairs here: two closed boundaries
    /// sharing a face at the same hand, which no orientation-preserving transport identifies —
    /// §IV's chirality, counted rather than silently bonded.
    pub fn self_contacts_refused(&self) -> u64 {
        self.self_contacts_refused
    }
    /// `(identity, storage ordinal, causal rank)` for every declared occurrence.
    pub fn causal_ranks(&self) -> &[(String, u64, u32)] {
        &self.causal_ranks
    }

    /// The pairs on which the corpus's causal order and its storage order disagree.
    ///
    /// Each entry is `(earlier identity, later identity)` where the storage ordinal runs one way
    /// and the causal rank runs the other, or where storage separates two occurrences that the
    /// causal order does not. An empty return is not a defect; it is the honest statement that on
    /// *this* material the two happen to agree, and it must be reported as such rather than left
    /// to imply that `⪯` was taken from adjacency.
    pub fn dependency_disagrees_with_storage(&self) -> Vec<(String, String)> {
        let mut disagreements = Vec::new();
        for (at, left) in self.causal_ranks.iter().enumerate() {
            for right in self.causal_ranks.iter().skip(at + 1) {
                let storage_ascends = left.1 < right.1;
                let causal_ascends = left.2 < right.2;
                let causal_level = left.2 == right.2;
                if causal_level || storage_ascends != causal_ascends {
                    disagreements.push((left.0.clone(), right.0.clone()));
                }
            }
        }
        disagreements
    }

    /// Found the grain-0 complex from declared material.
    ///
    /// `patch_extent` is the caller's declared aperture on how many inscription patches of each
    /// occurrence participate. It is a caller declaration, not an authored level, and the
    /// population it excluded is returned by [`Self::patches_outside_extent`].
    pub fn found(
        occurrences: &[DeclaredOccurrence],
        patch_extent: usize,
    ) -> Result<Self, IncidenceProductionError> {
        Self::found_inner(occurrences, patch_extent, None)
    }

    /// Found the same complex while retaining one declared exterior face per admitted adjacent
    /// patch pair. The face is lineage, never the internal reaction class.
    pub fn found_with_contact_faces(
        occurrences: &[DeclaredOccurrence],
        patch_extent: usize,
        contact_faces: &[Vec<DeclaredContactFace>],
    ) -> Result<Self, IncidenceProductionError> {
        Self::found_inner(occurrences, patch_extent, Some(contact_faces))
    }

    fn found_inner(
        occurrences: &[DeclaredOccurrence],
        patch_extent: usize,
        contact_faces: Option<&[Vec<DeclaredContactFace>]>,
    ) -> Result<Self, IncidenceProductionError> {
        if occurrences.is_empty() || patch_extent == 0 {
            return Err(IncidenceProductionError::NoDeclaredMaterial);
        }
        if contact_faces.is_some_and(|faces| faces.len() != occurrences.len()) {
            return Err(IncidenceProductionError::ContactFaceExtent);
        }
        let ranks = causal_ranks(occurrences)?;

        let mut site_index = BTreeMap::<(u32, String), usize>::new();
        let mut sites = Vec::<Site>::new();
        let mut bond_index = BTreeMap::<(usize, usize), usize>::new();
        let mut bonds = Vec::<Bond>::new();
        let mut self_contacts_refused = 0u64;
        let mut patches_outside_extent = 0u64;

        for (at, occurrence) in occurrences.iter().enumerate() {
            let rank = ranks[at];
            let complete = occurrence.inscription.len();
            if complete == 0 {
                return Err(IncidenceProductionError::EmptyOccurrence(
                    occurrence.identity.clone(),
                ));
            }
            patches_outside_extent = patches_outside_extent
                .checked_add(complete.saturating_sub(patch_extent) as u64)
                .ok_or(IncidenceProductionError::Extent)?;
            let expected_faces = complete.min(patch_extent).saturating_sub(1);
            let declared_faces = contact_faces.map(|faces| &faces[at]);
            if declared_faces.is_some_and(|faces| faces.len() != expected_faces) {
                return Err(IncidenceProductionError::ContactFaceExtent);
            }

            let mut previous: Option<usize> = None;
            for (patch_at, patch) in occurrence.inscription.iter().take(patch_extent).enumerate() {
                let key = (rank, patch.identity().to_owned());
                let at_site = match site_index.get(&key) {
                    Some(found) => {
                        sites[*found].occurrences = sites[*found]
                            .occurrences
                            .checked_add(1)
                            .ok_or(IncidenceProductionError::Extent)?;
                        *found
                    }
                    None => {
                        let ordinal = sites.len();
                        sites.push(Site {
                            id: EventCellId::new(0),
                            surface: patch.identity().to_owned(),
                            octets: patch.octets().to_vec(),
                            causal_rank: rank,
                            grain: 0,
                            octet_winding: octet_winding(patch.octets()),
                            occurrences: 1,
                        });
                        site_index.insert(key, ordinal);
                        ordinal
                    }
                };
                if let Some(prior) = previous {
                    if prior == at_site {
                        self_contacts_refused += 1;
                    } else {
                        let face = declared_faces
                            .map(|faces| faces[patch_at - 1].clone())
                            .unwrap_or_else(DeclaredContactFace::inscription_adjacency);
                        found_bond(
                            &mut bonds,
                            &mut bond_index,
                            &sites,
                            prior,
                            at_site,
                            rank,
                            0,
                            BTreeSet::from([face]),
                        )?;
                    }
                }
                previous = Some(at_site);
            }
        }
        if bonds.is_empty() {
            return Err(IncidenceProductionError::NoContact);
        }

        let dependencies = derive_dependencies(&sites);

        Self::assemble(
            0,
            sites,
            bonds,
            dependencies,
            patch_extent,
            patches_outside_extent,
            self_contacts_refused,
            occurrences
                .iter()
                .enumerate()
                .map(|(at, occurrence)| {
                    (
                        occurrence.identity.clone(),
                        occurrence.storage_ordinal,
                        ranks[at],
                    )
                })
                .collect(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn assemble(
        grain: u32,
        mut sites: Vec<Site>,
        mut bonds: Vec<Bond>,
        dependencies: Vec<(usize, usize)>,
        patch_extent: usize,
        patches_outside_extent: u64,
        self_contacts_refused: u64,
        causal_ranks: Vec<(String, u64, u32)>,
    ) -> Result<Self, IncidenceProductionError> {
        let compounds = fundamental_cycles(&sites, &bonds, grain)?;

        // Event-local addresses. Storage position never orders anything; these are addresses only.
        let mut ordinal = 0u64;
        for site in sites.iter_mut() {
            site.id = EventCellId::new(ordinal);
            ordinal += 1;
        }
        for bond in bonds.iter_mut() {
            bond.id = EventCellId::new(ordinal);
            ordinal += 1;
        }
        let mut compounds = compounds;
        for compound in compounds.iter_mut() {
            compound.id = EventCellId::new(ordinal);
            ordinal += 1;
        }

        let mut incoming = vec![0u64; sites.len()];
        let mut outgoing = vec![0u64; sites.len()];
        for bond in &bonds {
            outgoing[bond.from] += 1;
            incoming[bond.to] += 1;
        }
        for (before, after) in &dependencies {
            outgoing[*before] += 1;
            incoming[*after] += 1;
        }
        let mut ingress = (0..sites.len())
            .filter(|at| incoming[*at] == 0)
            .collect::<Vec<_>>();
        let ingress_was_declared = ingress.is_empty();
        if ingress_was_declared {
            ingress.push(0);
        }
        let mut exposed = (0..sites.len())
            .filter(|at| outgoing[*at] == 0)
            .collect::<Vec<_>>();
        let exposed_was_declared = exposed.is_empty();
        if exposed_was_declared {
            exposed.push(sites.len() - 1);
        }
        if exposed.is_empty() {
            return Err(IncidenceProductionError::NoExposedBoundary);
        }

        Ok(Self {
            grain,
            sites,
            bonds,
            compounds,
            dependencies,
            ingress,
            exposed,
            ingress_was_declared,
            exposed_was_declared,
            patch_extent,
            patches_outside_extent,
            self_contacts_refused,
            causal_ranks,
        })
    }

    // -----------------------------------------------------------------------------------------
    // `∂∂ = 0`, checked by the body's own organ
    // -----------------------------------------------------------------------------------------

    /// The cells, incidences and ports this complex presents to `body::incidence`.
    ///
    /// `sorted` chooses whether the three slices are handed over in the body's indexed order or in
    /// an arbitrary one. Both must validate and both must emanate the same node: that is §II's
    /// *"changing storage order without changing incidence or dependency must not change
    /// `T_gamma`"*, and it is the storage-order gauge control.
    pub fn event_parts(
        &self,
        sorted: bool,
    ) -> (Vec<EventCell>, Vec<OrientedIncidence>, Vec<EventPort>) {
        let mut cells =
            Vec::with_capacity(self.sites.len() + self.bonds.len() + self.compounds.len());
        for site in &self.sites {
            cells.push(EventCell::situated(
                site.id,
                site.causal_rank,
                0,
                site.grain,
                Cog::lit(site.surface.len() as i64),
            ));
        }
        for bond in &self.bonds {
            cells.push(EventCell::situated(
                bond.id,
                bond.causal_rank,
                1,
                bond.grain,
                Cog::lit(bond.multiplicity as i64),
            ));
        }
        for compound in &self.compounds {
            cells.push(EventCell::situated(
                compound.id,
                compound.causal_rank,
                2,
                compound.grain,
                Cog::lit(compound.bonds.len() as i64),
            ));
        }

        let mut incidences = Vec::new();
        for bond in &self.bonds {
            incidences.push(OrientedIncidence::boundary(
                self.sites[bond.from].id,
                bond.id,
                IncidenceHand::Against,
                0,
            ));
            incidences.push(OrientedIncidence::boundary(
                self.sites[bond.to].id,
                bond.id,
                IncidenceHand::With,
                1,
            ));
        }
        for compound in &self.compounds {
            for (slot, (at, hand)) in compound.bonds.iter().zip(compound.hands.iter()).enumerate() {
                incidences.push(OrientedIncidence::boundary(
                    self.bonds[*at].id,
                    compound.id,
                    *hand,
                    slot as u32,
                ));
            }
        }
        let mut dependency_slot = BTreeMap::<u64, u32>::new();
        for (before, after) in &self.dependencies {
            let target = self.sites[*after].id;
            let slot = dependency_slot.entry(target.ordinal()).or_default();
            incidences.push(OrientedIncidence::dependency(
                self.sites[*before].id,
                target,
                IncidenceHand::With,
                *slot,
            ));
            *slot += 1;
        }

        let mut ports = Vec::new();
        for (slot, at) in self.ingress.iter().enumerate() {
            ports.push(EventPort::ingress(
                self.sites[*at].id,
                IncidenceHand::With,
                slot as u32,
            ));
        }
        for (slot, at) in self.exposed.iter().enumerate() {
            ports.push(EventPort::exposed(
                self.sites[*at].id,
                IncidenceHand::With,
                slot as u32,
            ));
        }

        if sorted {
            cells.sort_by_key(|cell| cell.id().ordinal());
            incidences.sort_by_key(|incidence| (incidence.to().ordinal(), incidence.slot()));
            ports.sort_by_key(|port| (matches!(port.kind(), EventPortKind::Exposed), port.slot()));
        } else {
            cells.reverse();
            incidences.reverse();
        }
        (cells, incidences, ports)
    }

    /// Hand the complex to `body::incidence::EventComplex`, whose validator is the `∂∂ = 0` check.
    ///
    /// This module owns no second validator and no second complex.
    pub fn validate_with_body(&self, sorted: bool) -> Result<(), IncidenceProductionError> {
        let (cells, incidences, ports) = self.event_parts(sorted);
        EventComplex::new(&cells, &incidences, &ports).map_err(IncidenceProductionError::Body)?;
        Ok(())
    }

    /// The outer grain the body reads off the declared exposed boundary. Always `grain + 1`.
    pub fn body_outer_grain(&self) -> Result<u32, IncidenceProductionError> {
        let (cells, incidences, ports) = self.event_parts(true);
        let complex = EventComplex::new(&cells, &incidences, &ports)
            .map_err(IncidenceProductionError::Body)?;
        complex
            .outer_grain()
            .map_err(IncidenceProductionError::Body)
    }

    /// The two exposed-boundary readings `body::incidence` supplies, under both storage orders.
    /// Equal returns are the gauge statement; unequal ones would be a defect in this module.
    pub fn emanated_under_both_storage_orders(
        &self,
    ) -> Result<(u64, u64), IncidenceProductionError> {
        let mut read = [0u64; 2];
        for (at, sorted) in [true, false].into_iter().enumerate() {
            let (cells, incidences, ports) = self.event_parts(sorted);
            let complex = EventComplex::new(&cells, &incidences, &ports)
                .map_err(IncidenceProductionError::Body)?;
            let node = complex
                .emanated_node()
                .map_err(IncidenceProductionError::Body)?;
            read[at] = (node.well.face() as u64) ^ u64::from(node.len);
        }
        Ok((read[0], read[1]))
    }

    /// Reverse one contact's declared hand: `∂bond` becomes `from − to` instead of `to − from`.
    /// The two endpoint constituents are untouched.
    pub fn with_reversed_bond(&self, at: usize) -> Result<Self, IncidenceProductionError> {
        let mut bonds = self.bonds.clone();
        let bond = bonds.get_mut(at).ok_or(IncidenceProductionError::Extent)?;
        std::mem::swap(&mut bond.from, &mut bond.to);
        bond.contact_winding = contact_winding(
            self.sites[bond.from].surface.as_bytes(),
            self.sites[bond.to].surface.as_bytes(),
        );
        bond.sheet = sheet_of(self.sites[bond.to].surface.as_bytes());
        Self::assemble(
            self.grain,
            self.sites.clone(),
            bonds,
            self.dependencies.clone(),
            self.patch_extent,
            self.patches_outside_extent,
            self.self_contacts_refused,
            self.causal_ranks.clone(),
        )
    }

    /// Present the complex to the body with **one 2-cell's traversal hand flipped**, keeping every
    /// endpoint. The body must refuse: the flipped hand breaks `∂∂ = 0` at the two constituents
    /// that contact carries.
    pub fn body_refuses_flipped_compound_hand(
        &self,
        compound: usize,
        edge: usize,
    ) -> Result<EventComplexError, IncidenceProductionError> {
        let (cells, mut incidences, ports) = self.event_parts(true);
        let target = self
            .compounds
            .get(compound)
            .ok_or(IncidenceProductionError::Extent)?;
        let bond = *target
            .bonds
            .get(edge)
            .ok_or(IncidenceProductionError::Extent)?;
        let hand = target.hands[edge];
        let bond_id = self.bonds[bond].id;
        let mut flipped = false;
        for incidence in incidences.iter_mut() {
            if incidence.from() == bond_id && incidence.to() == target.id {
                *incidence = OrientedIncidence::boundary(
                    bond_id,
                    target.id,
                    hand.reversed(),
                    incidence.slot(),
                );
                flipped = true;
            }
        }
        if !flipped {
            return Err(IncidenceProductionError::Extent);
        }
        match EventComplex::new(&cells, &incidences, &ports) {
            Ok(_) => Err(IncidenceProductionError::Body(
                EventComplexError::InvalidBoundary(bond_id, target.id),
            )),
            Err(refusal) => Ok(refusal),
        }
    }

    // -----------------------------------------------------------------------------------------
    // Routes, vertices, interference
    // -----------------------------------------------------------------------------------------

    /// Every admitted route from `source`, to a declared depth.
    ///
    /// A route is a **simple** oriented path: no constituent is visited twice and no contact is
    /// crossed twice. A contact may be crossed against its hand — that is what makes `o_t` do
    /// work — but a dependency may only be crossed forward, because `⪯` is chronology and
    /// chronology has a parity.
    pub fn routes_from(
        &self,
        source: usize,
        depth: usize,
        chart: PhaseChart,
    ) -> Result<Vec<Route>, IncidenceProductionError> {
        let mut incident = vec![Vec::<Passage>::new(); self.sites.len()];
        for (at, bond) in self.bonds.iter().enumerate() {
            incident[bond.from].push(Passage::Bond {
                at,
                to: bond.to,
                hand: IncidenceHand::With,
            });
            incident[bond.to].push(Passage::Bond {
                at,
                to: bond.from,
                hand: IncidenceHand::Against,
            });
        }
        for (at, (before, after)) in self.dependencies.iter().enumerate() {
            incident[*before].push(Passage::Dependency { at, to: *after });
        }

        let mut rotations = Vec::with_capacity(self.bonds.len() + self.dependencies.len());
        for bond in &self.bonds {
            rotations.push(chart.contact_transport(bond.contact_winding, bond.sheet)?);
        }
        for (before, after) in &self.dependencies {
            let from = self.sites[*before].surface.as_bytes();
            let to = self.sites[*after].surface.as_bytes();
            rotations.push(chart.contact_transport(contact_winding(from, to), sheet_of(to))?);
        }

        let mut found = Vec::new();
        let mut visited = vec![false; self.sites.len()];
        let mut path = Vec::new();
        visited[source] = true;
        self.walk(
            source,
            source,
            depth,
            &incident,
            &rotations,
            &mut visited,
            &mut path,
            &mut found,
        );
        Ok(found)
    }

    #[allow(clippy::too_many_arguments)]
    fn walk(
        &self,
        source: usize,
        at: usize,
        remaining: usize,
        incident: &[Vec<Passage>],
        rotations: &[ExactWavePhaseTransport],
        visited: &mut [bool],
        path: &mut Vec<Passage>,
        found: &mut Vec<Route>,
    ) {
        if remaining == 0 {
            return;
        }
        for passage in &incident[at] {
            let next = passage.target();
            if visited[next] {
                continue;
            }
            visited[next] = true;
            path.push(*passage);
            found.push(self.route(source, path, rotations));
            self.walk(
                source,
                next,
                remaining - 1,
                incident,
                rotations,
                visited,
                path,
                found,
            );
            path.pop();
            visited[next] = false;
        }
    }

    /// Where a passage's carried transport sits in the per-chart table: contacts first, then the
    /// `⪯` edges. An address, never an order.
    const fn rotation_address(&self, passage: Passage) -> usize {
        match passage {
            Passage::Bond { at, .. } => at,
            Passage::Dependency { at, .. } => self.bonds.len() + at,
        }
    }

    fn route(
        &self,
        source: usize,
        path: &[Passage],
        rotations: &[ExactWavePhaseTransport],
    ) -> Route {
        let mut sites = Vec::with_capacity(path.len() + 1);
        sites.push(source);
        for passage in path {
            sites.push(passage.target());
        }
        let mut hand_parity = 1i8;
        let mut rotation = ExactWavePhaseTransport::identity();
        for passage in path {
            let carried = &rotations[self.rotation_address(*passage)];
            if passage.hand().coefficient() < 0 {
                hand_parity = -hand_parity;
                rotation = rotation.compose(&carried.inverse());
            } else {
                rotation = rotation.compose(carried);
            }
        }
        let mut amplitude = rotation.transport(&unit_current());
        if hand_parity < 0 {
            amplitude = ExactComplexWaveCurrent::new(-amplitude.real, -amplitude.imaginary);
        }
        Route {
            source,
            target: *sites.last().expect("a route retains its arrival"),
            sites,
            passages: path.to_vec(),
            hand_parity,
            rotation,
            amplitude,
        }
    }

    /// The word this route reads off the material.
    pub fn route_surface(&self, route: &Route) -> String {
        let mut surface = String::new();
        for (at, site) in route.sites.iter().enumerate() {
            if at != 0 {
                surface.push(' ');
                surface.push_str(match route.passages[at - 1] {
                    Passage::Bond {
                        hand: IncidenceHand::With,
                        ..
                    } => "→",
                    Passage::Bond {
                        hand: IncidenceHand::Against,
                        ..
                    } => "←",
                    Passage::Dependency { .. } => "⪯",
                });
                surface.push(' ');
            }
            surface.push_str(&self.sites[*site].surface);
        }
        surface
    }

    /// Superpose every route arriving at one constituent, through the engine's own organ.
    ///
    /// `ExactReceiverPhasePopulation::receive` sums same-mode currents **before** any quadratic
    /// response is formed, so the cross term is formed by the engine and not by this module. A
    /// count could not have produced any of the four numbers this returns.
    pub fn interfere(&self, routes: &[Route], target: usize, mode: u64) -> Interference {
        let mode = DimensionalWaveModeId(mode);
        let mut population = ExactReceiverPhasePopulation::default();
        let mut arriving = Vec::new();
        let mut tape = rat(0);
        for route in routes.iter().filter(|route| route.target == target) {
            population.receive(mode, &route.amplitude);
            tape = tape + route.amplitude.norm_square();
            arriving.push(route.clone());
        }
        let sum = population
            .coherent_modes
            .get(&mode)
            .cloned()
            .unwrap_or_else(ExactComplexWaveCurrent::zero);
        let tower = sum.norm_square();
        let cross_term = &tower - &tape;
        let cancelled = arriving.len() > 1 && sum.is_zero() && tape != rat(0);

        // §IV, Annihilation: *"opposed contributions in one declared fiber actually compose to
        // zero."* The pair is the unit the law names, and the engine forms it: two currents
        // received into one mode leave the population empty. A flat, inactive, equal, absent or
        // uncontacted relation is not thereby annihilated, which is why the guard requires both
        // amplitudes to be non-zero and the pair to be distinct routes.
        let mut annihilating = Vec::new();
        for (left, first) in arriving.iter().enumerate() {
            for (right, second) in arriving.iter().enumerate().skip(left + 1) {
                if first.amplitude.is_zero() || second.amplitude.is_zero() {
                    continue;
                }
                let mut pair = ExactReceiverPhasePopulation::default();
                pair.receive(mode, &first.amplitude);
                pair.receive(mode, &second.amplitude);
                if pair.coherent_modes.is_empty() {
                    annihilating.push((left, right));
                }
            }
        }
        Interference {
            target,
            routes: arriving,
            sum,
            tape_reading: tape,
            tower_reading: tower,
            cross_term,
            cancelled,
            annihilating_pairs: annihilating,
        }
    }

    /// Every arrival of one route population, grouped by the constituent it arrives at.
    ///
    /// The same reading as [`Self::interfere`] taken once per constituent instead of once per
    /// candidate pair of indices, so a wider declared material stays reachable.
    pub fn interfere_all(&self, routes: &[Route], mode: u64) -> Vec<Interference> {
        let mut by_target = BTreeMap::<usize, Vec<Route>>::new();
        for route in routes {
            by_target
                .entry(route.target)
                .or_default()
                .push(route.clone());
        }
        let mut found = Vec::with_capacity(by_target.len());
        for (target, arriving) in by_target {
            found.push(self.interfere(&arriving, target, mode));
        }
        found
    }

    /// The negative control on cancellation: the same currents, one mode each.
    ///
    /// `ExactReceiverPhasePopulation`'s own doctrine is that distinct modes stay separate, so two
    /// currents that annihilate in one mode must both survive in two. If this returned a collapse,
    /// the cancellation above would be an addressing accident rather than interference.
    pub fn mode_separated_population(routes: &[Route]) -> ExactReceiverPhasePopulation {
        let mut population = ExactReceiverPhasePopulation::default();
        for (at, route) in routes.iter().enumerate() {
            population.receive(DimensionalWaveModeId(at as u64), &route.amplitude);
        }
        population
    }

    // -----------------------------------------------------------------------------------------
    // Holonomy and hand-up
    // -----------------------------------------------------------------------------------------

    /// The transport carried once around a closed internal boundary.
    ///
    /// Returns `(chain gauge, holonomy)`.
    ///
    /// The **holonomy** is the ordered composition of the contact transports around the closed
    /// boundary, each inverted where the boundary crosses its contact against the declared hand.
    /// Traversing the loop the other way returns the exact inverse, so *identity* — flatness — is
    /// a direction-invariant property of the compound and not of the walk that found it.
    ///
    /// The **chain gauge** is `Π o(e)` over the boundary. It is returned beside the holonomy and
    /// is deliberately not part of it: on an odd-length closed boundary it flips with the
    /// traversal direction, so it is a coordinate of the 2-chain, not an invariant of the cell.
    pub fn holonomy(
        &self,
        compound: usize,
        chart: PhaseChart,
    ) -> Result<(i8, ExactWavePhaseTransport), IncidenceProductionError> {
        let target = self
            .compounds
            .get(compound)
            .ok_or(IncidenceProductionError::Extent)?;
        let mut parity = 1i8;
        let mut rotation = ExactWavePhaseTransport::identity();
        for (at, hand) in target.bonds.iter().zip(target.hands.iter()) {
            let bond = &self.bonds[*at];
            let carried = chart.contact_transport(bond.contact_winding, bond.sheet)?;
            if hand.coefficient() < 0 {
                parity = -parity;
                rotation = rotation.compose(&carried.inverse());
            } else {
                rotation = rotation.compose(&carried);
            }
        }
        Ok((parity, rotation))
    }

    /// `complete_{F,Q,k}(C_k) → (n_{k+1}, ρ_k)`.
    ///
    /// Every completed compound emits **one** atomic successor at grain `k+1`, carrying its
    /// residual. It is not a population of branches: one closed internal boundary, one
    /// constituent, one residual.
    pub fn hand_up(&self, chart: PhaseChart) -> Result<Vec<Emission>, IncidenceProductionError> {
        let mut emissions = Vec::with_capacity(self.compounds.len());
        for (at, compound) in self.compounds.iter().enumerate() {
            let (parity, rotation) = self.holonomy(at, chart)?;
            let internal = compound.bonds.iter().copied().collect::<BTreeSet<_>>();
            let on_cycle = compound.sites.iter().copied().collect::<BTreeSet<_>>();

            let mut surface = String::new();
            for (position, site) in compound.sites.iter().enumerate() {
                if position != 0 {
                    surface.push(' ');
                }
                surface.push_str(&self.sites[*site].surface);
            }

            let mut exposed = Vec::new();
            for site in &compound.sites {
                let mut donates = false;
                let mut accepts = false;
                for (bond_at, bond) in self.bonds.iter().enumerate() {
                    if internal.contains(&bond_at) {
                        continue;
                    }
                    if bond.from == *site {
                        donates = true;
                    }
                    if bond.to == *site {
                        accepts = true;
                    }
                }
                for (before, after) in &self.dependencies {
                    if before == site {
                        donates = true;
                    }
                    if after == site {
                        accepts = true;
                    }
                }
                let polarity = match (donates, accepts) {
                    (true, true) => Some(ExposedPolarity::Both),
                    (true, false) => Some(ExposedPolarity::Donor),
                    (false, true) => Some(ExposedPolarity::Acceptor),
                    (false, false) => None,
                };
                if let Some(polarity) = polarity {
                    exposed.push((self.sites[*site].surface.clone(), polarity));
                }
            }

            let mut departed = Vec::with_capacity(compound.bonds.len());
            let mut carried = 0u64;
            for bond_at in &compound.bonds {
                let bond = &self.bonds[*bond_at];
                departed.push(format!(
                    "{} ⟶ {}",
                    self.sites[bond.from].surface, self.sites[bond.to].surface
                ));
                carried = carried.saturating_add(bond.multiplicity);
            }

            emissions.push(Emission {
                grain: self.grain + 1,
                causal_rank: compound.causal_rank,
                surface,
                chain_gauge: parity,
                holonomy: rotation,
                residual: Residual {
                    exposed,
                    departed_contacts: departed,
                    internal_contacts: compound.bonds.len(),
                    carried_multiplicity: carried,
                    sites_departed: on_cycle.len(),
                },
            });
        }
        Ok(emissions)
    }

    /// Close every internal boundary, hand up, and found the grain-`k+1` complex.
    ///
    /// Two emitted constituents bond where **an actual contact of this complex leaves one's closed
    /// boundary and arrives at the other's**, and that contact is internal to neither — so
    /// removing or reversing it changes later lawful transport. §IV is explicit that *mere
    /// adjacency is not a bond*, and sharing an exposed constituent's **name** is adjacency: an
    /// earlier form of this method bonded on the shared name and the constituent population
    /// **expanded** `12 → 48 → 2054` instead of contracting, because nearly every pair of
    /// compounds shares a function word. The contact is the bond; the name is not.
    ///
    /// Nothing here reads any emission's position in the returned slice.
    pub fn next_grain(
        &self,
        chart: PhaseChart,
    ) -> Result<(Vec<Emission>, Self), IncidenceProductionError> {
        let emissions = self.hand_up(chart)?;
        if emissions.is_empty() {
            return Err(IncidenceProductionError::NoDeclaredMaterial);
        }
        let grain = self.grain + 1;
        let mut sites = Vec::with_capacity(emissions.len());
        for emission in &emissions {
            sites.push(Site {
                id: EventCellId::new(0),
                surface: emission.surface.clone(),
                // A grade-`k+1` constituent is founded from the emission handed up by a completed
                // compound, not from exterior material, so its own carrier is that emission's
                // surface. The codec's cut applies at grade 0 only.
                octets: emission.surface.as_bytes().to_vec(),
                causal_rank: emission.causal_rank,
                grain,
                octet_winding: octet_winding(emission.surface.as_bytes()),
                occurrences: 1,
            });
        }

        let boundary = self
            .compounds
            .iter()
            .map(|compound| {
                let mut hands = BTreeMap::new();
                for (at, hand) in compound.bonds.iter().zip(compound.hands.iter()) {
                    hands.insert(*at, *hand);
                }
                (
                    compound.sites.iter().copied().collect::<BTreeSet<_>>(),
                    hands,
                )
            })
            .collect::<Vec<_>>();

        let mut bonds = Vec::new();
        let mut bond_index = BTreeMap::new();
        let mut incoherent = 0u64;
        for (left, donor) in boundary.iter().enumerate() {
            for (right, acceptor) in boundary.iter().enumerate() {
                if left == right
                    || self.compounds[left].causal_rank != self.compounds[right].causal_rank
                {
                    continue;
                }
                // Species one: the two closed boundaries SHARE a contact. Two 2-cells meeting
                // along a 1-cell is the gluing face, and the orientation is solved rather than
                // read off any order — the donor is the one that crosses the shared face along
                // its hand while the acceptor crosses it against. Equal hands do not glue
                // coherently; that is a chirality obstruction and is counted, not bonded.
                let mut glued = false;
                let mut contact_faces = BTreeSet::new();
                for (at, hand) in donor.1.iter() {
                    if let Some(other) = acceptor.1.get(at) {
                        if *hand == other.reversed() {
                            glued |= hand.coefficient() > 0;
                            if hand.coefficient() > 0 {
                                contact_faces.extend(self.bonds[*at].contact_faces.iter().cloned());
                            }
                        } else {
                            incoherent += 1;
                        }
                    }
                }
                // Species two: a contact of this complex LEAVES one closed boundary and ARRIVES at
                // the other, and is internal to neither. §IV: removing or reversing it changes
                // later lawful transport.
                let mut crossing = false;
                for (at, bond) in self.bonds.iter().enumerate() {
                    if !donor.1.contains_key(&at)
                        && !acceptor.1.contains_key(&at)
                        && donor.0.contains(&bond.from)
                        && acceptor.0.contains(&bond.to)
                    {
                        crossing = true;
                        contact_faces.extend(bond.contact_faces.iter().cloned());
                    }
                }
                if glued || crossing {
                    found_bond(
                        &mut bonds,
                        &mut bond_index,
                        &sites,
                        left,
                        right,
                        self.compounds[left].causal_rank,
                        grain,
                        contact_faces,
                    )?;
                }
            }
        }
        if bonds.is_empty() {
            return Err(IncidenceProductionError::NoContact);
        }
        let mut next = Self::assemble(grain, sites, bonds, Vec::new(), 0, 0, 0, Vec::new())?;
        next.self_contacts_refused = incoherent;
        Ok((emissions, next))
    }

    /// Why the tower stopped: the census of every candidate pair [`Self::next_grain`] considered.
    ///
    /// A pair may be refused for one of exactly three reasons, and they are different findings.
    /// `refused_by_causal_rank` is a **law** refusal — the method requires two compounds to sit at
    /// the same rank in `⪯` before it will even look at their boundaries. `refused_unbonded` is a
    /// **material** refusal: the two closed boundaries neither share a face nor are joined by a
    /// contact of this complex. Reporting one as the other is how a construction question gets
    /// mistaken for a scale question.
    pub fn next_grain_census(&self) -> NextGrainCensus {
        let boundary = self
            .compounds
            .iter()
            .map(|compound| {
                let mut hands = BTreeMap::new();
                for (at, hand) in compound.bonds.iter().zip(compound.hands.iter()) {
                    hands.insert(*at, *hand);
                }
                (
                    compound.sites.iter().copied().collect::<BTreeSet<_>>(),
                    hands,
                )
            })
            .collect::<Vec<_>>();

        let mut census = NextGrainCensus {
            compounds: self.compounds.len(),
            ..NextGrainCensus::default()
        };
        for (left, donor) in boundary.iter().enumerate() {
            for (right, acceptor) in boundary.iter().enumerate() {
                if left == right {
                    continue;
                }
                census.pairs_considered += 1;
                let same_rank =
                    self.compounds[left].causal_rank == self.compounds[right].causal_rank;
                let mut glued = false;
                for (at, hand) in donor.1.iter() {
                    if let Some(other) = acceptor.1.get(at) {
                        if *hand == other.reversed() {
                            glued |= hand.coefficient() > 0;
                        } else if same_rank {
                            census.incoherent += 1;
                        }
                    }
                }
                let crossing = self.bonds.iter().enumerate().any(|(at, bond)| {
                    !donor.1.contains_key(&at)
                        && !acceptor.1.contains_key(&at)
                        && donor.0.contains(&bond.from)
                        && acceptor.0.contains(&bond.to)
                });
                if !same_rank {
                    census.refused_by_causal_rank += 1;
                    // The counterfactual, and it is a pure measurement of the boundaries that are
                    // already there: how many of the pairs the rank guard refused **before looking**
                    // would have bonded had it looked. Non-zero means the guard is the binding
                    // constraint and the tower's ceiling is in the LAW. Zero means the material had
                    // nothing there anyway and the ceiling is in the MATERIAL. Nothing here changes
                    // what `next_grain` does; the counterfactual is reported, never conducted.
                    if glued || crossing {
                        census.would_bond_across_rank += 1;
                    }
                    continue;
                }
                census.same_rank += 1;
                if glued {
                    census.glued += 1;
                }
                if crossing {
                    census.crossing += 1;
                }
                if glued || crossing {
                    census.bonded += 1;
                } else {
                    census.refused_unbonded += 1;
                }
            }
        }
        census
    }

    // -----------------------------------------------------------------------------------------
    // Differentiation — the formal partner of closure
    // -----------------------------------------------------------------------------------------

    /// The same cells, handed to `holonic_engine::algebraic::GradedCausalComplex`.
    ///
    /// A second complex is not built: the sites, contacts and closed boundaries are the ones this
    /// module already carries, presented in the engine's carrier so that
    /// `holonic_engine::running_integral` can act on them. `found_cell` re-checks `∂∂ = 0` on
    /// construction, so this is a **third independent frame** on the same law —
    /// `body::incidence::EventComplex` is the second — and a disagreement between any two of them
    /// is a defect in this module rather than a fact about the material.
    pub fn engine_view(&self) -> Result<EngineView, IncidenceProductionError> {
        let mut complex = GradedCausalComplex::default();
        let mut site_cells = Vec::with_capacity(self.sites.len());
        for site in &self.sites {
            let id = complex
                .found_cell(
                    site.surface.clone(),
                    BTreeSet::from([EventId(u64::from(site.causal_rank))]),
                    0,
                    CausalChain::default(),
                )
                .map_err(|error| IncidenceProductionError::Engine(format!("{error}")))?;
            site_cells.push(id);
        }
        let mut bond_cells = Vec::with_capacity(self.bonds.len());
        for bond in &self.bonds {
            // `∂bond = to − from`, exactly as `event_parts` presents it to the body.
            let mut chain = CausalChain::default();
            chain.add_term(site_cells[bond.to], ComparativeMultiplicity::positive(1u32));
            chain.add_term(
                site_cells[bond.from],
                ComparativeMultiplicity::negative(1u32),
            );
            let id = complex
                .found_cell(
                    format!(
                        "{} ⟶ {}",
                        self.sites[bond.from].surface, self.sites[bond.to].surface
                    ),
                    BTreeSet::from([EventId(u64::from(bond.causal_rank))]),
                    1,
                    chain,
                )
                .map_err(|error| IncidenceProductionError::Engine(format!("{error}")))?;
            bond_cells.push(id);
        }
        let mut compound_cells = Vec::with_capacity(self.compounds.len());
        for compound in &self.compounds {
            let mut chain = CausalChain::default();
            for (at, hand) in compound.bonds.iter().zip(compound.hands.iter()) {
                chain.add_term(
                    bond_cells[*at],
                    match hand {
                        IncidenceHand::With => ComparativeMultiplicity::positive(1u32),
                        IncidenceHand::Against => ComparativeMultiplicity::negative(1u32),
                    },
                );
            }
            let id = complex
                .found_cell(
                    self.compound_surface(compound),
                    BTreeSet::from([EventId(u64::from(compound.causal_rank))]),
                    2,
                    chain,
                )
                .map_err(|error| IncidenceProductionError::Engine(format!("{error}")))?;
            compound_cells.push(id);
        }
        complex
            .validate()
            .map_err(|error| IncidenceProductionError::Engine(format!("{error}")))?;
        Ok(EngineView {
            complex,
            sites: site_cells,
            bonds: bond_cells,
            compounds: compound_cells,
        })
    }

    /// The declared 1-cochain: `w(e) = sheet(e) · contact_winding(e)`, exact in `ℤ`.
    ///
    /// This is the **additive** reading of the same two material numbers the multiplicative
    /// transport uses — how far the contact crosses, and onto which sheet. It is a different
    /// reading of the same contact, not a second material: `PhaseChart::rotation` is not a
    /// homomorphism out of `(ℤ,+)`, so the additive residual and the multiplicative holonomy are
    /// two frames on one closed boundary and their agreement is a measurement, never an assumption.
    pub fn winding_cochain(&self, view: &EngineView) -> Cochain {
        Cochain::from_values(
            1,
            self.bonds.iter().enumerate().map(|(at, bond)| {
                (
                    view.bonds[at],
                    BigInt::from(i64::from(bond.sheet) * i64::from(bond.contact_winding)),
                )
            }),
        )
    }

    fn compound_surface(&self, compound: &Compound) -> String {
        let mut surface = String::new();
        for (position, site) in compound.sites.iter().enumerate() {
            if position != 0 {
                surface.push(' ');
            }
            surface.push_str(&self.sites[*site].surface);
        }
        surface
    }

    /// `differentiate_k(n_{k+1}) → (∂Σ, r_Σ, supp_Σ)`.
    ///
    /// Closure suppressed a compound's internal boundary: `hand_up` names those contacts as
    /// **departed** and the higher-grain constituent stands in their place. Differentiation
    /// restores them. It is the formal partner of closure in the strict sense, because the two are
    /// adjoint:
    ///
    /// ```text
    ///     ⟨w, ∂Σ⟩  =  ⟨dw, Σ⟩
    /// ```
    ///
    /// The left side is this module walking the closed boundary in traversal order; the right side
    /// is `holonic_engine::running_integral::coboundary` summing over the engine's own unordered
    /// boundary chain. [`Differentiation::stokes_holds`] is that identity taken as a check.
    ///
    /// `supp_Σ` is the part of `∂Σ` the residual is **supported on** — the contacts carrying a
    /// non-zero winding. It is where a later arrival can reach this compound, and it is strictly
    /// narrower than the boundary: a contact crossing zero bits carries no potential difference and
    /// nothing composes there.
    pub fn differentiate(
        &self,
        at: usize,
        chart: PhaseChart,
        view: &EngineView,
        cochain: &Cochain,
    ) -> Result<Differentiation, IncidenceProductionError> {
        let compound = self
            .compounds
            .get(at)
            .ok_or(IncidenceProductionError::Extent)?;
        let (chain_gauge, holonomy) = self.holonomy(at, chart)?;

        let mut reexposed = Vec::with_capacity(compound.bonds.len());
        let mut residual = BigInt::from(0);
        let mut support = BTreeSet::new();
        let mut support_contacts = Vec::new();
        for (position, (bond_at, hand)) in
            compound.bonds.iter().zip(compound.hands.iter()).enumerate()
        {
            let bond = &self.bonds[*bond_at];
            let carried = i64::from(bond.sheet) * i64::from(bond.contact_winding);
            residual += BigInt::from(hand.coefficient() * carried);
            if carried != 0 {
                support.insert(bond.from);
                support.insert(bond.to);
                support_contacts.push(*bond_at);
            }
            reexposed.push(ReexposedContact {
                position,
                bond: *bond_at,
                from: self.sites[bond.from].surface.clone(),
                to: self.sites[bond.to].surface.clone(),
                hand: *hand,
                carried,
            });
        }

        // `(dw)(Σ) = w(∂Σ)`: the engine evaluates the cochain on its own boundary chain for this
        // one cell. [`Self::differentiate_all`] takes the whole coboundary at once and overwrites
        // this, so both the per-cell pairing and the total `d` are exercised.
        let cell = view
            .complex
            .cell(view.compounds[at])
            .map_err(|error| IncidenceProductionError::Engine(format!("{error}")))?;
        let coboundary_reading = cochain
            .evaluate(&view.complex, &cell.boundary)
            .map_err(|error| IncidenceProductionError::Integral(format!("{error}")))?;

        Ok(Differentiation {
            compound: at,
            surface: self.compound_surface(compound),
            causal_rank: compound.causal_rank,
            reexposed,
            residual,
            coboundary_reading,
            chain_gauge,
            holonomy,
            support: support.into_iter().collect(),
            support_contacts,
        })
    }

    /// [`Self::differentiate`] over every closed boundary, with the engine view built once.
    pub fn differentiate_all(
        &self,
        chart: PhaseChart,
    ) -> Result<Vec<Differentiation>, IncidenceProductionError> {
        let view = self.engine_view()?;
        let cochain = self.winding_cochain(&view);
        let differentiated = coboundary(&view.complex, &cochain)
            .map_err(|error| IncidenceProductionError::Integral(format!("{error}")))?;
        let mut found = Vec::with_capacity(self.compounds.len());
        for at in 0..self.compounds.len() {
            let mut one = self.differentiate(at, chart, &view, &cochain)?;
            one.coboundary_reading = differentiated.value(view.compounds[at]);
            found.push(one);
        }
        Ok(found)
    }

    /// The chord population the **engine's** spanning tree finds, over every component.
    ///
    /// This module's [`fundamental_cycles`] and `running_integral`'s `found_potential_in` walk two
    /// independently built spanning forests, so the two chord sets are different bases of the same
    /// cycle space. What must agree across them is not the basis — a basis is a receiver-visible
    /// coordinate — but the **image of the holonomy homomorphism `H₁ → ℤ`**, which is the subgroup
    /// generated by the residuals and is therefore named by their gcd. That is the two-frame check
    /// `CLAUDE.md` §0's fourth lesson asks for, and it can fail.
    pub fn chord_population(
        &self,
        group: &CoefficientGroup,
    ) -> Result<ChordPopulation, IncidenceProductionError> {
        let view = self.engine_view()?;
        let cochain = self.winding_cochain(&view);
        let mut reached = BTreeSet::<CausalCellId>::new();
        let mut retained = Vec::<ChordObstruction>::new();
        let mut agreeing = 0usize;
        let mut bases = Vec::new();
        for (at, cell) in view.sites.iter().enumerate() {
            if reached.contains(cell) {
                continue;
            }
            let search = found_potential_in(&view.complex, &cochain, *cell, group.clone())
                .map_err(|error| IncidenceProductionError::Integral(format!("{error}")))?;
            reached.extend(search.reached.iter().copied());
            agreeing += search.agreeing_chords.len();
            retained.extend(search.retained_obstructions.iter().cloned());
            bases.push((at, self.sites[at].surface.clone(), search.cycle_rank()));
        }
        let mut image = BigInt::from(0);
        for chord in &retained {
            image = exact_gcd(&image, &chord.residual);
        }
        Ok(ChordPopulation {
            components: bases.len(),
            bases,
            cycle_rank: agreeing + retained.len(),
            agreeing,
            retained,
            image,
        })
    }

    /// `⟨w, Σ nᵢ ∂Σᵢ⟩` — the residual of a `ℤ`-combination of closed boundaries, evaluated by
    /// `holonic_engine::running_integral::Cochain::evaluate` on the combined 1-chain.
    ///
    /// **This is what makes the residual causal rather than reported.** The pairing is linear on
    /// the cycle space, so when a later arrival founds a new closed boundary `Σ'` through a
    /// standing one `Σ`, the two are related by
    ///
    /// ```text
    ///     r(Σ' − Σ)  =  r(Σ') − r(Σ)
    /// ```
    ///
    /// and therefore `Σ` hands its **whole** obstruction into every cycle it enters, while a
    /// **saturated** compound — `r_Σ = 0` — hands forward exactly nothing. That is
    /// `canon/THE_MEASURED_CAPABILITIES.md` M7, *a complete obstruction causes the next
    /// construction*, together with its converse: a vanishing obstruction causes nothing, and
    /// neither half is authored here. The left-hand side is computed by the engine on a chain this
    /// module never sums; the right-hand side by this module walking two boundaries. They are two
    /// frames on one number.
    pub fn residual_of_combination(
        &self,
        terms: &[(usize, i64)],
    ) -> Result<BigInt, IncidenceProductionError> {
        let view = self.engine_view()?;
        self.residual_of_combination_in(terms, &view)
    }

    /// [`Self::residual_of_combination`] with the engine view built once by the caller.
    pub fn residual_of_combination_in(
        &self,
        terms: &[(usize, i64)],
        view: &EngineView,
    ) -> Result<BigInt, IncidenceProductionError> {
        let cochain = self.winding_cochain(view);
        let mut chain = CausalChain::default();
        for (at, coefficient) in terms {
            let compound = self
                .compounds
                .get(*at)
                .ok_or(IncidenceProductionError::Extent)?;
            for (bond_at, hand) in compound.bonds.iter().zip(compound.hands.iter()) {
                let signed = coefficient.saturating_mul(hand.coefficient());
                if signed == 0 {
                    continue;
                }
                let magnitude = signed.unsigned_abs();
                chain.add_term(
                    view.bonds[*bond_at],
                    if signed > 0 {
                        ComparativeMultiplicity::positive(magnitude)
                    } else {
                        ComparativeMultiplicity::negative(magnitude)
                    },
                );
            }
        }
        cochain
            .evaluate(&view.complex, &chain)
            .map_err(|error| IncidenceProductionError::Integral(format!("{error}")))
    }

    /// The same image, read off **this module's own** fundamental-cycle basis.
    pub fn holonomy_image(&self, chart: PhaseChart) -> Result<BigInt, IncidenceProductionError> {
        let mut image = BigInt::from(0);
        for differentiation in self.differentiate_all(chart)? {
            image = exact_gcd(&image, &differentiation.residual);
        }
        Ok(image)
    }

    // -----------------------------------------------------------------------------------------
    // Response to later material
    // -----------------------------------------------------------------------------------------

    /// The arrival's place in `⪯`, derived from the declared family's own `caused_by` relation.
    ///
    /// Nothing chooses it. An arrival whose causes are all present at rank `r` sits at `r+1`; an
    /// arrival with no cause inside the family sits at rank zero, **co-present with the roots**. An
    /// arrival naming a cause the family does not carry is refused rather than silently made a
    /// root, because that would turn a caused occurrence into an uncaused one to keep a method
    /// total.
    pub fn arrival_rank(
        &self,
        arrival: &DeclaredOccurrence,
    ) -> Result<u32, IncidenceProductionError> {
        let mut rank = 0u32;
        for cause in &arrival.caused_by {
            let found = self
                .causal_ranks
                .iter()
                .find(|(identity, _, _)| identity == cause)
                .ok_or_else(|| {
                    IncidenceProductionError::ArrivalCauseIsOutsideTheFamily(cause.clone())
                })?;
            rank = rank.max(found.2.saturating_add(1));
        }
        Ok(rank)
    }

    /// **The reopening law**, as stated, and then as the run corrected it.
    ///
    /// ```text
    ///   Σ REOPENS  ⟺  the arrival founds a passage incident to a constituent of supp_Σ
    ///                 AND  r_Σ ≠ 0  in the declared coefficient group
    /// ```
    ///
    /// `reopened`, `saturated` and `untouched` partition the standing closed boundaries by that
    /// rule. **What the rule turned out to predict is not what it was written to predict**, and
    /// each verdict carries both readings so the difference stays visible:
    ///
    /// - It does **not** predict that a closed boundary moves, because none ever does. Adding
    ///   cells to a graph cannot destroy a cycle, so a completed compound is permanent under any
    ///   arrival. [`ClosureVerdict::moved`] is measured every run and is a constant `false`; that
    ///   is what *closed* means and it is the honest content of `complete_{F,Q,k}` being a
    ///   completion rather than a stage.
    /// - **Reaching** predicts the **valence**: [`ClosureVerdict::predicted_valence_move`] fires
    ///   where a passage that did not exist lands on a constituent of `∂Σ` not already at
    ///   [`ExposedPolarity::Both`], and it was right on every closed boundary of all three declared
    ///   arrivals.
    /// - The **residual** predicts the **transport**. `⟨w, ·⟩` is linear on the cycle space, so
    ///   `r(Σ' − Σ) = r(Σ') − r(Σ)`: a compound hands its whole obstruction into every cycle the
    ///   arrival founds through it, and a **saturated** one hands forward exactly nothing. That is
    ///   `canon/THE_MEASURED_CAPABILITIES.md` M7 — *a complete obstruction causes the next
    ///   construction* — with its converse made checkable, and both halves are theorems rather than
    ///   rules authored here. [`Self::residual_of_combination`] computes the left-hand side through
    ///   the engine.
    ///
    /// The complete re-derivation is taken every run and compared against the prediction, because a
    /// differential update whose prediction is never checked is a claim about code rather than a
    /// measurement of it (`CLAUDE.md` §8). Cost is counted in cells, never in elapsed time.
    pub fn admit_later(
        &self,
        arrival: &DeclaredOccurrence,
        chart: PhaseChart,
        group: &CoefficientGroup,
    ) -> Result<ArrivalResponse, IncidenceProductionError> {
        if self.patch_extent == 0 {
            // A complex above grain zero carries no inscription aperture, so an arrival has no
            // patches to found. Refused rather than silently admitted as an empty occurrence.
            return Err(IncidenceProductionError::Extent);
        }
        if self
            .causal_ranks
            .iter()
            .any(|(identity, _, _)| identity == &arrival.identity)
        {
            // Admitting one identity twice would double its deposit and make the withdrawal a
            // partial inverse, which is exactly the accumulation the falsifier is looking for.
            return Err(IncidenceProductionError::EmptyOccurrence(
                arrival.identity.clone(),
            ));
        }
        let rank = self.arrival_rank(arrival)?;
        let before = self.hand_up(chart)?;
        let differentiated = self.differentiate_all(chart)?;

        let mut sites = self.sites.clone();
        let mut bonds = self.bonds.clone();
        let mut site_index = BTreeMap::<(u32, String), usize>::new();
        for (at, site) in sites.iter().enumerate() {
            site_index.insert((site.causal_rank, site.surface.clone()), at);
        }
        let mut bond_index = BTreeMap::<(usize, usize), usize>::new();
        for (at, bond) in bonds.iter().enumerate() {
            bond_index.insert((bond.from, bond.to), at);
        }
        let base_sites = sites.len();
        let base_bonds = bonds.len();

        let complete = arrival.inscription.len();
        if complete == 0 {
            return Err(IncidenceProductionError::EmptyOccurrence(
                arrival.identity.clone(),
            ));
        }
        let mut trace = ArrivalTrace {
            identity: arrival.identity.clone(),
            rank,
            base_sites,
            base_bonds,
            base_patches_outside_extent: self.patches_outside_extent,
            base_self_contacts_refused: self.self_contacts_refused,
            site_occurrence_delta: BTreeMap::new(),
            bond_multiplicity_delta: BTreeMap::new(),
        };

        let mut previous: Option<usize> = None;
        let mut self_contacts = self.self_contacts_refused;
        for patch in arrival.inscription.iter().take(self.patch_extent) {
            let key = (rank, patch.identity().to_owned());
            let at_site = match site_index.get(&key) {
                Some(found) => {
                    sites[*found].occurrences = sites[*found]
                        .occurrences
                        .checked_add(1)
                        .ok_or(IncidenceProductionError::Extent)?;
                    *trace.site_occurrence_delta.entry(*found).or_default() += 1;
                    *found
                }
                None => {
                    let ordinal = sites.len();
                    sites.push(Site {
                        id: EventCellId::new(0),
                        surface: patch.identity().to_owned(),
                        octets: patch.octets().to_vec(),
                        causal_rank: rank,
                        grain: self.grain,
                        octet_winding: octet_winding(patch.octets()),
                        occurrences: 1,
                    });
                    site_index.insert(key, ordinal);
                    ordinal
                }
            };
            if let Some(prior) = previous {
                if prior == at_site {
                    self_contacts += 1;
                } else {
                    let existing = bond_index.get(&(prior, at_site)).copied();
                    found_bond(
                        &mut bonds,
                        &mut bond_index,
                        &sites,
                        prior,
                        at_site,
                        rank,
                        self.grain,
                        BTreeSet::from([DeclaredContactFace::inscription_adjacency()]),
                    )?;
                    if let Some(found) = existing {
                        *trace.bond_multiplicity_delta.entry(found).or_default() += 1;
                    }
                }
            }
            previous = Some(at_site);
        }

        let dependencies = derive_dependencies(&sites);
        let base_dependencies = self.dependencies.iter().copied().collect::<BTreeSet<_>>();
        let new_dependencies = dependencies
            .iter()
            .copied()
            .filter(|edge| !base_dependencies.contains(edge))
            .collect::<Vec<_>>();

        // Every constituent a new passage touches. A `⪯` edge is a passage: the arrival reaches an
        // earlier compound along the corpus's own causal order, which is exactly the relation §I
        // insists is distinct from adjacency.
        //
        // The two species are kept apart because they do different work, which the run measured.
        // `touched_by_new_cell` is a constituent that acquired a passage it did not have; that is
        // what can change a valence. A **re-tread** raises `Π` on a contact that was already there
        // and adds no port, so it reaches the compound without changing what it exposes.
        let mut touched_by_new_cell = BTreeSet::<usize>::new();
        for bond in bonds.iter().skip(base_bonds) {
            touched_by_new_cell.insert(bond.from);
            touched_by_new_cell.insert(bond.to);
        }
        for (before_at, after_at) in &new_dependencies {
            touched_by_new_cell.insert(*before_at);
            touched_by_new_cell.insert(*after_at);
        }
        let mut touched = touched_by_new_cell.clone();
        for at in trace.bond_multiplicity_delta.keys() {
            touched.insert(bonds[*at].from);
            touched.insert(bonds[*at].to);
        }

        let mut reached = Vec::new();
        let mut reopened = Vec::new();
        let mut saturated = Vec::new();
        let mut untouched = Vec::new();
        for differentiation in &differentiated {
            let meets = differentiation
                .support
                .iter()
                .any(|site| touched.contains(site));
            if !meets {
                untouched.push(differentiation.compound);
                continue;
            }
            reached.push(differentiation.compound);
            if group.vanishes(&differentiation.residual) {
                saturated.push(differentiation.compound);
            } else {
                reopened.push(differentiation.compound);
            }
        }

        let mut causal_ranks = self.causal_ranks.clone();
        causal_ranks.push((arrival.identity.clone(), arrival.storage_ordinal, rank));
        let admitted = Self::assemble(
            self.grain,
            sites,
            bonds,
            dependencies,
            self.patch_extent,
            self.patches_outside_extent
                .checked_add(complete.saturating_sub(self.patch_extent) as u64)
                .ok_or(IncidenceProductionError::Extent)?,
            self_contacts,
            causal_ranks,
        )?;

        let after = admitted.hand_up(chart)?;

        // The law made a prediction per closed boundary. It is now checked against the complete
        // re-derivation, every run. `CLAUDE.md` §8: a check whose material cannot vary the property
        // under test is the same defect as a check that cannot fail — so the prediction is
        // recorded first and compared second, and the confusion matrix is the return.
        let mut standing = BTreeMap::<Vec<(String, String)>, usize>::new();
        for at in 0..after.len() {
            standing.insert(admitted.closed_boundary_address(at), at);
        }
        let mut verdicts = Vec::with_capacity(before.len());
        let mut founded_addresses = standing.keys().cloned().collect::<BTreeSet<_>>();
        for (at, emission) in before.iter().enumerate() {
            let address = self.closed_boundary_address(at);
            founded_addresses.remove(&address);
            let predicted_to_transport = reopened.contains(&at);
            // The valence prediction is a different question and consults a different set: a
            // constituent of the whole closed boundary, touched by a passage that did not exist,
            // **and not already at `Both`**. Polarity is a three-valued reading of the ports a
            // constituent presents, so a constituent already donating and accepting cannot move by
            // acquiring a further passage. Predicting without that clause scored 8 of 10 twice, in
            // both cases on a compound whose only touched constituent was the recurring function
            // word, and the two misses were the same miss.
            let standing_polarity = emission
                .residual
                .exposed
                .iter()
                .cloned()
                .collect::<BTreeMap<_, _>>();
            let predicted_valence_move = self.compounds[at].sites.iter().any(|site| {
                touched_by_new_cell.contains(site)
                    && standing_polarity.get(&self.sites[*site].surface)
                        != Some(&ExposedPolarity::Both)
            });
            let (moved, valence_moved, after_emission) = match standing.get(&address) {
                None => (true, true, None),
                Some(found) => (
                    after[*found].closed_boundary_reading() != emission.closed_boundary_reading(),
                    after[*found].frame_reading().1 != emission.frame_reading().1,
                    Some(after[*found].clone()),
                ),
            };
            verdicts.push(ClosureVerdict {
                compound: at,
                surface: emission.surface.clone(),
                predicted_to_transport,
                predicted_valence_move,
                moved,
                valence_moved,
                before: emission.clone(),
                after: after_emission,
            });
        }
        let founded = founded_addresses
            .iter()
            .filter_map(|address| standing.get(address))
            .map(|at| after[*at].clone())
            .collect::<Vec<_>>();
        let dissolved = verdicts
            .iter()
            .filter(|verdict| verdict.after.is_none())
            .map(|verdict| verdict.before.clone())
            .collect::<Vec<_>>();

        Ok(ArrivalResponse {
            arrival: arrival.identity.clone(),
            arrival_rank: rank,
            arrival_is_co_present: self
                .causal_ranks
                .iter()
                .any(|(_, _, existing)| *existing == rank),
            reached,
            reopened,
            saturated,
            untouched,
            before,
            after,
            founded,
            dissolved,
            verdicts,
            new_contacts: admitted.bonds.len() - base_bonds,
            new_constituents: admitted.sites.len() - base_sites,
            new_dependencies: new_dependencies.len(),
            complex: admitted,
            trace,
        })
    }

    /// The closed boundary's address, independent of the spanning forest that found it and of any
    /// storage position: the sorted multiset of its oriented contacts, named by surface and rank.
    ///
    /// Two complexes agree on a compound exactly when they agree on this, which is what lets a
    /// differential update recognise the cell it is carrying.
    pub fn closed_boundary_address(&self, at: usize) -> Vec<(String, String)> {
        let Some(compound) = self.compounds.get(at) else {
            return Vec::new();
        };
        let mut address = compound
            .bonds
            .iter()
            .map(|bond_at| {
                let bond = &self.bonds[*bond_at];
                (
                    format!(
                        "{}@{}",
                        self.sites[bond.from].surface, self.sites[bond.from].causal_rank
                    ),
                    format!(
                        "{}@{}",
                        self.sites[bond.to].surface, self.sites[bond.to].causal_rank
                    ),
                )
            })
            .collect::<Vec<_>>();
        address.sort();
        address
    }

    /// Withdraw an admitted arrival: remove exactly the cells and multiplicities it deposited.
    ///
    /// This is the inverse of [`Self::admit_later`] on the **admitted** complex, not a re-founding
    /// from the original material. It therefore tests something a re-founding cannot: that nothing
    /// accumulated. If a multiplicity, an occurrence count or a `⪯` edge were retained, the
    /// withdrawn complex would emit differently from the base and the falsifier fires.
    pub fn withdraw(&self, trace: &ArrivalTrace) -> Result<Self, IncidenceProductionError> {
        let mut sites = self.sites.clone();
        let mut bonds = self.bonds.clone();
        for (at, delta) in &trace.site_occurrence_delta {
            let site = sites.get_mut(*at).ok_or(IncidenceProductionError::Extent)?;
            site.occurrences = site
                .occurrences
                .checked_sub(*delta)
                .ok_or(IncidenceProductionError::Extent)?;
        }
        for (at, delta) in &trace.bond_multiplicity_delta {
            let bond = bonds.get_mut(*at).ok_or(IncidenceProductionError::Extent)?;
            bond.multiplicity = bond
                .multiplicity
                .checked_sub(*delta)
                .ok_or(IncidenceProductionError::Extent)?;
        }
        sites.truncate(trace.base_sites);
        bonds.truncate(trace.base_bonds);
        let dependencies = derive_dependencies(&sites);
        let causal_ranks = self
            .causal_ranks
            .iter()
            .filter(|(identity, _, _)| identity != &trace.identity)
            .cloned()
            .collect::<Vec<_>>();
        Self::assemble(
            self.grain,
            sites,
            bonds,
            dependencies,
            self.patch_extent,
            trace.base_patches_outside_extent,
            trace.base_self_contacts_refused,
            causal_ranks,
        )
    }
}

// ---------------------------------------------------------------------------------------------
// Routes
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Passage {
    Bond {
        at: usize,
        to: usize,
        hand: IncidenceHand,
    },
    Dependency {
        at: usize,
        to: usize,
    },
}

impl Passage {
    pub const fn target(self) -> usize {
        match self {
            Self::Bond { to, .. } | Self::Dependency { to, .. } => to,
        }
    }

    pub const fn hand(self) -> IncidenceHand {
        match self {
            Self::Bond { hand, .. } => hand,
            Self::Dependency { .. } => IncidenceHand::With,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Route {
    pub source: usize,
    pub target: usize,
    pub sites: Vec<usize>,
    pub passages: Vec<Passage>,
    pub hand_parity: i8,
    pub rotation: ExactWavePhaseTransport,
    pub amplitude: ExactComplexWaveCurrent,
}

/// The vertex, read: what the routes arriving at one constituent do to each other.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interference {
    pub target: usize,
    pub routes: Vec<Route>,
    /// `Σ α`, formed by `ExactReceiverPhasePopulation::receive` before any quadratic response.
    pub sum: ExactComplexWaveCurrent,
    /// `Σ |α|²` — the count. The tower with the relation switched off; Pythagoras.
    pub tape_reading: Rat,
    /// `|Σ α|²` — the tower.
    pub tower_reading: Rat,
    /// `2 Re(α₁ ᾱ₂) + …` — the cross term, which is the Feynman vertex (`H.0216`).
    pub cross_term: Rat,
    /// The **complete** arriving fiber summed to zero. Rarer and stronger than a pair.
    pub cancelled: bool,
    /// Indices into `routes` of the pairs that annihilate exactly — §IV's unit.
    pub annihilating_pairs: Vec<(usize, usize)>,
}

impl Interference {
    /// The two amplitudes of one annihilating pair, and what a count would have read instead.
    ///
    /// `(|α_i|² + |α_j|², |α_i + α_j|², cross term)`. The cross term is exactly `−(|α_i|²+|α_j|²)`:
    /// the whole of the tape reading, deleted by the relation the tape cannot carry.
    pub fn pair_reading(&self, pair: (usize, usize)) -> (Rat, Rat, Rat) {
        let first = &self.routes[pair.0].amplitude;
        let second = &self.routes[pair.1].amplitude;
        let tape = first.norm_square() + second.norm_square();
        let summed = ExactComplexWaveCurrent::new(
            &first.real + &second.real,
            &first.imaginary + &second.imaginary,
        );
        let tower = summed.norm_square();
        let cross = &tower - &tape;
        (tape, tower, cross)
    }
}

// ---------------------------------------------------------------------------------------------
// Closure
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Residual {
    /// The compound's remaining external boundary, by constituent and polarity.
    pub exposed: Vec<(String, ExposedPolarity)>,
    /// The contacts that closed and departed as separate constituents.
    pub departed_contacts: Vec<String>,
    pub internal_contacts: usize,
    pub carried_multiplicity: u64,
    pub sites_departed: usize,
}

/// One atomic successor at grain `k+1`, with its residual named.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Emission {
    pub grain: u32,
    pub causal_rank: u32,
    pub surface: String,
    /// `Π o(e)` around the closed boundary — the 2-chain's own gauge, not an invariant. Carried
    /// so it can be seen, never read as curvature.
    pub chain_gauge: i8,
    pub holonomy: ExactWavePhaseTransport,
    pub residual: Residual,
}

impl Emission {
    /// A compound whose transport around its own closed boundary is the identity sits on flat
    /// terrain. Anything else retained holonomy. Direction-invariant: the reverse traversal
    /// returns the inverse, and the identity is its own inverse.
    pub fn terrain_is_flat(&self) -> bool {
        self.holonomy == ExactWavePhaseTransport::identity()
    }

    pub fn holonomy_text(&self) -> String {
        format!("({}, {})", self.holonomy.cosine, self.holonomy.sine)
    }

    /// **What closure fixed.** The closed boundary itself: its traversal, its transport, its
    /// enclosed contacts. Only a reopening changes any of this.
    pub fn closed_boundary_reading(
        &self,
    ) -> (&str, &ExactWavePhaseTransport, i8, usize, usize, &[String]) {
        (
            &self.surface,
            &self.holonomy,
            self.chain_gauge,
            self.residual.internal_contacts,
            self.residual.sites_departed,
            &self.residual.departed_contacts,
        )
    }

    /// **What is a present-frame reading, and always refreshes.**
    ///
    /// `Π`, the lived construction — `carried_multiplicity` — is frequency, and `CLAUDE.md` §13
    /// rule 2 is explicit that frequency *"is apart of the machine's mechanics"* and not the
    /// assistant's to gate. `Γ`, the exposed boundary with its polarities, is valence, and the
    /// ratified law §IV says valence *"is receiver-relative, not a permanent integer stored on an
    /// information object."* Neither is fixed by closure, so neither is evidence that a compound
    /// reopened, and reading a refreshed count as a reopening would be exactly the count-standing-
    /// in-for-a-return the tape record convicted.
    pub fn frame_reading(&self) -> (u64, &[(String, ExposedPolarity)]) {
        (self.residual.carried_multiplicity, &self.residual.exposed)
    }
}

// ---------------------------------------------------------------------------------------------
// Differentiation
// ---------------------------------------------------------------------------------------------

/// The same cells in `holonic_engine`'s algebraic carrier, with this module's indices mapped over.
#[derive(Clone, Debug)]
pub struct EngineView {
    complex: GradedCausalComplex,
    sites: Vec<CausalCellId>,
    bonds: Vec<CausalCellId>,
    compounds: Vec<CausalCellId>,
}

impl EngineView {
    pub fn complex(&self) -> &GradedCausalComplex {
        &self.complex
    }
    pub fn site(&self, at: usize) -> Option<CausalCellId> {
        self.sites.get(at).copied()
    }
    pub fn bond(&self, at: usize) -> Option<CausalCellId> {
        self.bonds.get(at).copied()
    }
    pub fn compound(&self, at: usize) -> Option<CausalCellId> {
        self.compounds.get(at).copied()
    }
}

/// One contact of a closed boundary, restored by differentiation.
///
/// `hand_up` named this contact as **departed**: closure enclosed it and the higher-grain
/// constituent stands in its place. This is that contact handed back, oriented as the boundary
/// crossed it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReexposedContact {
    /// Where in the closed boundary's own traversal this crossing sits.
    pub position: usize,
    pub bond: usize,
    pub from: String,
    pub to: String,
    pub hand: IncidenceHand,
    /// `w(e) = sheet(e) · contact_winding(e)`, the additive reading of the turn the contact carries.
    pub carried: i64,
}

impl ReexposedContact {
    /// The declared contact, the hand the closed boundary crossed it at, and the turn it carries.
    ///
    /// The contact's own orientation and the traversal's hand are printed apart on purpose: `∂bond
    /// = to − from` is a property of the cell, while the crossing is a property of the walk, and
    /// collapsing them is how a chain gauge gets read as an invariant.
    pub fn text(&self) -> String {
        format!(
            "{} ⟶ {}   crossed {:<7}  w = {:+}",
            self.from,
            self.to,
            match self.hand {
                IncidenceHand::With => "with",
                IncidenceHand::Against => "against",
            },
            self.carried
        )
    }
}

/// `differentiate_k(n_{k+1}) → (∂Σ, r_Σ, supp_Σ)`: what closure suppressed, handed back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Differentiation {
    pub compound: usize,
    pub surface: String,
    pub causal_rank: u32,
    /// `∂Σ` — the oriented internal boundary, restored contact by contact.
    pub reexposed: Vec<ReexposedContact>,
    /// `⟨w, ∂Σ⟩`, summed by this module along the boundary's own traversal.
    pub residual: BigInt,
    /// `⟨dw, Σ⟩`, returned by `holonic_engine::running_integral::coboundary` over the engine's own
    /// unordered boundary chain. Stokes says these are one number.
    pub coboundary_reading: BigInt,
    pub chain_gauge: i8,
    pub holonomy: ExactWavePhaseTransport,
    /// The constituents the residual is supported on: endpoints of contacts carrying `w ≠ 0`.
    /// This is **where the compound can reopen**.
    pub support: Vec<usize>,
    pub support_contacts: Vec<usize>,
}

impl Differentiation {
    /// `⟨w, ∂Σ⟩ = ⟨dw, Σ⟩`, taken as a check across two frames.
    pub fn stokes_holds(&self) -> bool {
        self.residual == self.coboundary_reading
    }

    /// The multiplicative reading: the closed boundary returned the identity.
    pub fn holonomy_is_flat(&self) -> bool {
        self.holonomy == ExactWavePhaseTransport::identity()
    }

    /// The additive reading: the residual vanishes in the declared group.
    pub fn residual_vanishes(&self, group: &CoefficientGroup) -> bool {
        group.vanishes(&self.residual)
    }

    /// A compound with nothing for a later arrival to act on: transporting around it returns no
    /// potential difference, so the arrival reaches it and nothing is caused.
    pub fn is_saturated(&self, group: &CoefficientGroup) -> bool {
        self.residual_vanishes(group)
    }
}

/// The chord population the engine's own spanning forest returns, over every component.
#[derive(Clone, Debug)]
pub struct ChordPopulation {
    pub components: usize,
    /// `(site index, surface, cycle rank of that component)` for each base the sweep declared.
    pub bases: Vec<(usize, String, usize)>,
    pub cycle_rank: usize,
    pub agreeing: usize,
    pub retained: Vec<ChordObstruction>,
    /// The generator of the image of `H₁ → ℤ`: basis-free, and the invariant two frames must share.
    pub image: BigInt,
}

// ---------------------------------------------------------------------------------------------
// Response to later material
// ---------------------------------------------------------------------------------------------

/// Exactly what a later arrival deposited, so that it can be taken back out again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArrivalTrace {
    pub identity: String,
    pub rank: u32,
    pub base_sites: usize,
    pub base_bonds: usize,
    pub base_patches_outside_extent: u64,
    pub base_self_contacts_refused: u64,
    /// Existing constituents whose occurrence count the arrival raised, and by how much.
    pub site_occurrence_delta: BTreeMap<usize, u64>,
    /// Existing contacts whose multiplicity the arrival raised, and by how much.
    pub bond_multiplicity_delta: BTreeMap<usize, u64>,
}

/// What the reopening law predicted for one closed boundary, and what the material did.
///
/// The two are recorded separately and compared, because a differential update whose prediction is
/// never checked against the complete re-derivation is a claim about code rather than a
/// measurement of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureVerdict {
    pub compound: usize,
    pub surface: String,
    /// The law said this compound hands its obstruction into whatever the arrival founds through
    /// it: it was reached at the support of its residual, and that residual does not vanish.
    pub predicted_to_transport: bool,
    /// The law said this compound's **valence** changes: a passage that did not exist now lands on
    /// a constituent of its closed boundary.
    pub predicted_valence_move: bool,
    /// Its closed boundary actually moved, or vanished entirely.
    ///
    /// **This can only ever be `false` for an arrival.** Adding cells to a graph never destroys a
    /// cycle, so a closed boundary is permanent under later material — which is what *closed*
    /// means, and it is a theorem rather than a limit of this implementation. It is measured
    /// anyway, every run, because a theorem asserted is not a theorem checked.
    pub moved: bool,
    /// Its **valence** moved: the exposed ports it presents, or their polarity, are different.
    /// This is `Γ_t`, and §IV is explicit that it is *receiver-relative, not a permanent integer*.
    pub valence_moved: bool,
    pub before: Emission,
    /// `None` when the closed boundary no longer exists: the arrival's contact split it.
    pub after: Option<Emission>,
}

impl ClosureVerdict {
    /// The valence half of the law, scored.
    pub fn valence_law_was_right(&self) -> bool {
        self.predicted_valence_move == self.valence_moved
    }
}

/// What a later arrival did to a standing complex.
#[derive(Clone, Debug)]
pub struct ArrivalResponse {
    pub arrival: String,
    pub arrival_rank: u32,
    /// The arrival's derived rank coincides with a rank the family already carries, so it shares
    /// constituents and can found a contact **inside** an earlier closed boundary. An arrival at a
    /// new rank reaches back only along `⪯`.
    pub arrival_is_co_present: bool,
    /// Compounds a new passage touched at the support of their residual.
    pub reached: Vec<usize>,
    /// Of those, the ones whose residual does not vanish: these reopen.
    pub reopened: Vec<usize>,
    /// Reached, and saturated. The arrival got there and nothing was caused.
    pub saturated: Vec<usize>,
    pub untouched: Vec<usize>,
    pub before: Vec<Emission>,
    pub after: Vec<Emission>,
    /// Closed boundaries that did not exist before the arrival.
    pub founded: Vec<Emission>,
    /// Closed boundaries that no longer exist: the arrival's contact split them.
    pub dissolved: Vec<Emission>,
    /// One per standing closed boundary: what the law predicted, and what happened.
    pub verdicts: Vec<ClosureVerdict>,
    pub new_contacts: usize,
    pub new_constituents: usize,
    pub new_dependencies: usize,
    pub complex: IncidenceComplex,
    pub trace: ArrivalTrace,
}

impl ArrivalResponse {
    /// The load-bearing claim: a **named** earlier successor moved.
    pub fn moved(&self) -> Vec<&ClosureVerdict> {
        self.verdicts
            .iter()
            .filter(|verdict| verdict.moved)
            .collect()
    }

    /// The valence half of the law, scored over every standing closed boundary: `(right, wrong)`.
    pub fn valence_law_agreement(&self) -> (usize, usize) {
        let right = self
            .verdicts
            .iter()
            .filter(|verdict| verdict.valence_law_was_right())
            .count();
        (right, self.verdicts.len() - right)
    }

    /// Nothing about the standing body changed at all. This is what the saturated control returns.
    pub fn nothing_was_caused(&self) -> bool {
        self.before == self.after && self.founded.is_empty() && self.dissolved.is_empty()
    }

    /// No **closed boundary** moved.
    ///
    /// This is a theorem and not a hope: adding cells to a graph never destroys a cycle, so a
    /// closed boundary is permanent under any arrival. A count, a port polarity and the population
    /// of closed boundaries beside it may all still have moved — `Π` is the lived construction,
    /// `Γ` is a present-frame reading, and a newly founded cycle is the region growing. None of
    /// them is closure's to fix.
    pub fn no_closed_boundary_moved(&self) -> bool {
        self.verdicts.iter().all(|verdict| !verdict.moved)
    }
}

/// Why the tower stopped, per candidate pair of closed boundaries.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NextGrainCensus {
    pub compounds: usize,
    pub pairs_considered: usize,
    /// Refused before their boundaries were consulted, because the two compounds sit at different
    /// ranks in `⪯`. A **law** refusal.
    pub refused_by_causal_rank: usize,
    /// Of those, the pairs that would have bonded had the guard looked. This is the counterfactual
    /// that separates a law ceiling from a material ceiling, and it is measured rather than
    /// conducted: `next_grain` still refuses every one of them.
    pub would_bond_across_rank: usize,
    pub same_rank: usize,
    pub glued: usize,
    pub crossing: usize,
    pub bonded: usize,
    /// Same rank, and neither species fired. A **material** refusal.
    pub refused_unbonded: usize,
    pub incoherent: usize,
}

// ---------------------------------------------------------------------------------------------
// Material readings
// ---------------------------------------------------------------------------------------------

/// §III: the number of adjacent bit transitions across a constituent's own octet stream.
///
/// `s_i = (−1)^{b_i}`, `h_i = s_{i+1} s_i = (−1)^{b_i ⊕ b_{i+1}}`. Equal adjacent bits stay on one
/// sheet; a changed bit crosses to the opposed sheet. This counts the crossings.
pub fn octet_winding(inscription: &[u8]) -> u32 {
    let mut windings = 0u32;
    let mut previous: Option<bool> = None;
    for octet in inscription {
        for shift in (0..u8::BITS).rev() {
            let bit = (octet >> shift) & 1 == 1;
            if previous.is_some_and(|prior| prior != bit) {
                windings = windings.saturating_add(1);
            }
            previous = Some(bit);
        }
    }
    windings
}

/// The §III transition count carried across one contact: `popcount(tail(from) ⊕ head(to))`.
///
/// How far the contact crosses. It fixes the magnitude of the turn and says nothing about its
/// sense; [`sheet_of`] is the independent reading that does.
pub fn contact_winding(from: &[u8], to: &[u8]) -> u32 {
    let tail = from.last().copied().unwrap_or_default();
    let head = to.first().copied().unwrap_or_default();
    (tail ^ head).count_ones()
}

/// The §III sheet a contact lands on: `+1` when the arriving octet's own face is even, `−1` when
/// it is odd.
///
/// §III: *"Equal adjacent bits remain on one sheet; a changed bit crosses to the opposed sheet."*
/// The sense of a turn is which sheet you are on, and that is a different reading of the material
/// from how far you crossed. Their independence is what lets a closed boundary return to the
/// identity at all — a chart whose generators all turn one way has no flat loops and its curvature
/// receipt would carry no evidence.
pub fn sheet_of(inscription: &[u8]) -> i8 {
    let head = inscription.first().copied().unwrap_or_default();
    if head.count_ones() % 2 == 0 {
        1
    } else {
        -1
    }
}

/// `⪯`: one constituent recurring at a later causal rank.
///
/// This is the corpus's own causal order carried into the complex; nothing here consults storage
/// position. It is a pure function of the constituent population, which is what lets a later
/// arrival's dependency edges be derived and withdrawn rather than accumulated.
fn derive_dependencies(sites: &[Site]) -> Vec<(usize, usize)> {
    let mut by_surface = BTreeMap::<&str, Vec<usize>>::new();
    for (at, site) in sites.iter().enumerate() {
        by_surface
            .entry(site.surface.as_str())
            .or_default()
            .push(at);
    }
    let mut dependencies = Vec::new();
    for occurrences_of in by_surface.values() {
        let mut ordered = occurrences_of.clone();
        ordered.sort_by_key(|at| sites[*at].causal_rank);
        for pair in ordered.windows(2) {
            if sites[pair[0]].causal_rank < sites[pair[1]].causal_rank {
                dependencies.push((pair[0], pair[1]));
            }
        }
    }
    dependencies
}

/// The exact non-negative generator of the subgroup of `ℤ` two integers generate.
///
/// Euclid, on `BigInt`, with no float and no library that would import one. `gcd(0, 0) = 0`, which
/// is the correct reading: the trivial subgroup is generated by zero, and a cycle space every one
/// of whose residuals vanishes has a **zero** holonomy image rather than an undefined one.
fn exact_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let zero = BigInt::from(0);
    let mut a = if *left < zero {
        -left.clone()
    } else {
        left.clone()
    };
    let mut b = if *right < zero {
        -right.clone()
    } else {
        right.clone()
    };
    while b != zero {
        let remainder = &a % &b;
        a = b;
        b = remainder;
    }
    a
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn unit_current() -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(rat(1), rat(0))
}

#[allow(clippy::too_many_arguments)]
fn found_bond(
    bonds: &mut Vec<Bond>,
    index: &mut BTreeMap<(usize, usize), usize>,
    sites: &[Site],
    from: usize,
    to: usize,
    causal_rank: u32,
    grain: u32,
    contact_faces: BTreeSet<DeclaredContactFace>,
) -> Result<(), IncidenceProductionError> {
    if contact_faces.is_empty() {
        return Err(IncidenceProductionError::ContactFaceExtent);
    }
    match index.get(&(from, to)) {
        Some(at) => {
            bonds[*at].multiplicity = bonds[*at]
                .multiplicity
                .checked_add(1)
                .ok_or(IncidenceProductionError::Extent)?;
            bonds[*at].contact_faces.extend(contact_faces);
        }
        None => {
            index.insert((from, to), bonds.len());
            bonds.push(Bond {
                id: EventCellId::new(0),
                from,
                to,
                causal_rank,
                grain,
                contact_winding: contact_winding(&sites[from].octets, &sites[to].octets),
                sheet: sheet_of(&sites[to].octets),
                multiplicity: 1,
                contact_faces,
            });
        }
    }
    Ok(())
}

/// The longest-path rank of each occurrence in the declared family's own `caused_by` relation.
///
/// This is `⪯_t`. It consults no ordinal, no timestamp and no slice position. An occurrence whose
/// causes all lie outside the declared family is a root of the declared cut, which is the honest
/// reading: the cut is bounded and its outside is not present.
fn causal_ranks(occurrences: &[DeclaredOccurrence]) -> Result<Vec<u32>, IncidenceProductionError> {
    let mut index = BTreeMap::new();
    for (at, occurrence) in occurrences.iter().enumerate() {
        index.insert(occurrence.identity.as_str(), at);
    }
    let mut ranks = vec![0u32; occurrences.len()];
    for _ in 0..=occurrences.len() {
        let mut moved = false;
        for (at, occurrence) in occurrences.iter().enumerate() {
            for cause in &occurrence.caused_by {
                if let Some(source) = index.get(cause.as_str()) {
                    let candidate = ranks[*source].saturating_add(1);
                    if candidate > ranks[at] {
                        ranks[at] = candidate;
                        moved = true;
                    }
                }
            }
        }
        if !moved {
            return Ok(ranks);
        }
    }
    Err(IncidenceProductionError::CausalCycle)
}

/// The fundamental cycle basis of the contact graph: a spanning forest, and one cycle per chord.
///
/// The forest condenses for free — subtree equals interval, remainder empty — and every non-tree
/// contact forces exactly one further closed boundary. That forced population is the whole content
/// of the departure from a forest (`CLAUDE.md` §11), and it is what closure hands up.
fn fundamental_cycles(
    sites: &[Site],
    bonds: &[Bond],
    grain: u32,
) -> Result<Vec<Compound>, IncidenceProductionError> {
    let mut incident = vec![Vec::<(usize, usize)>::new(); sites.len()];
    for (at, bond) in bonds.iter().enumerate() {
        incident[bond.from].push((at, bond.to));
        incident[bond.to].push((at, bond.from));
    }

    // A spanning forest by breadth, recording each constituent's parent contact.
    let mut parent = vec![usize::MAX; sites.len()];
    let mut parent_bond = vec![usize::MAX; sites.len()];
    let mut depth = vec![0usize; sites.len()];
    let mut seen = vec![false; sites.len()];
    let mut tree = vec![false; bonds.len()];
    for root in 0..sites.len() {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut front = std::collections::VecDeque::new();
        front.push_back(root);
        while let Some(at) = front.pop_front() {
            for (bond, other) in &incident[at] {
                if seen[*other] {
                    continue;
                }
                seen[*other] = true;
                parent[*other] = at;
                parent_bond[*other] = *bond;
                depth[*other] = depth[at] + 1;
                tree[*bond] = true;
                front.push_back(*other);
            }
        }
    }

    let mut compounds = Vec::new();
    for (chord, bond) in bonds.iter().enumerate() {
        if tree[chord] {
            continue;
        }
        // The tree path from `to` back up to the meet with `from`, then down.
        let mut left = bond.from;
        let mut right = bond.to;
        let mut up_left = Vec::new();
        let mut up_right = Vec::new();
        while depth[left] > depth[right] {
            up_left.push(parent_bond[left]);
            left = parent[left];
        }
        while depth[right] > depth[left] {
            up_right.push(parent_bond[right]);
            right = parent[right];
        }
        while left != right {
            if parent[left] == usize::MAX || parent[right] == usize::MAX {
                break;
            }
            up_left.push(parent_bond[left]);
            left = parent[left];
            up_right.push(parent_bond[right]);
            right = parent[right];
        }
        if left != right {
            continue;
        }

        // The closed walk: `from` → (up the tree) → meet → (down the tree) → `to` → chord → `from`.
        let mut walk = Vec::with_capacity(up_left.len() + up_right.len() + 1);
        walk.extend(up_left.iter().copied());
        walk.extend(up_right.iter().rev().copied());
        walk.push(chord);

        let mut at = bond.from;
        let mut ordered_bonds = Vec::with_capacity(walk.len());
        let mut hands = Vec::with_capacity(walk.len());
        let mut ordered_sites = Vec::with_capacity(walk.len());
        let mut lawful = true;
        for step in &walk {
            let crossing = &bonds[*step];
            let (next, hand) = if crossing.from == at {
                (crossing.to, IncidenceHand::With)
            } else if crossing.to == at {
                (crossing.from, IncidenceHand::Against)
            } else {
                lawful = false;
                break;
            };
            ordered_bonds.push(*step);
            hands.push(hand);
            ordered_sites.push(next);
            at = next;
        }
        if !lawful || at != bond.from || ordered_bonds.len() < 2 {
            continue;
        }
        // One contact may not appear twice in one closed boundary: `∂∂ = 0` would still hold but
        // the compound would be a doubled cell rather than a cycle.
        let distinct = ordered_bonds.iter().copied().collect::<BTreeSet<_>>();
        if distinct.len() != ordered_bonds.len() {
            continue;
        }
        compounds.push(Compound {
            id: EventCellId::new(0),
            causal_rank: sites[bond.from].causal_rank,
            grain,
            chord,
            bonds: ordered_bonds,
            hands,
            sites: ordered_sites,
        });
    }
    if compounds.len() > bonds.len() {
        return Err(IncidenceProductionError::Extent);
    }
    Ok(compounds)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One occurrence whose patches are declared directly, bypassing the text codec.
    fn declared_patches(
        identity: &str,
        patches: &[(&[u8], &str)],
    ) -> Result<DeclaredOccurrence, IncidenceProductionError> {
        let mut inscription = Vec::new();
        for (octets, patch_identity) in patches {
            inscription.push(Patch::new(octets.to_vec(), *patch_identity)?);
        }
        Ok(DeclaredOccurrence {
            identity: identity.to_owned(),
            storage_ordinal: 0,
            caused_by: BTreeSet::new(),
            inscription,
        })
    }

    /// **The mouth admits a material whose carrier is not UTF-8 words, and reads its windings off
    /// the material's own octets.**
    ///
    /// Before 2026-08-13 this was not expressible: the organ cut `occurrence.text` on whitespace
    /// and took `octet_winding(patch.as_bytes())`, so any material had to present as a UTF-8 string
    /// and its windings were read off that presentation. Here the octets are two-octet words that
    /// are not valid text, and the identity is a short declared name whose own bytes carry a
    /// *different* winding — so a reading that had quietly fallen back to the identity would return
    /// the wrong number rather than merely failing.
    #[test]
    fn a_material_that_is_not_text_admits_and_its_windings_come_from_its_own_octets() {
        // 0xAA 0x55 alternates every bit: 7 transitions inside each octet, 0 across the join.
        let alternating: &[u8] = &[0xAA, 0x55];
        // The identity's own bytes carry 6, so the two readings are distinguishable.
        assert_eq!(octet_winding(alternating), 14);
        assert_eq!(octet_winding(b"w0"), 6);

        let occurrence = declared_patches(
            "weights:0",
            &[
                (alternating, "w0"),
                (&[0x00, 0xFF], "w1"),
                (alternating, "w0"),
            ],
        )
        .expect("declared patches");
        let complex = IncidenceComplex::found(&[occurrence], 3).expect("found a non-text complex");

        // Two distinct sites: the third patch is the first one recurring.
        assert_eq!(complex.sites().len(), 2);
        let first = complex
            .sites()
            .iter()
            .find(|site| site.surface == "w0")
            .expect("the declared identity names the site");
        assert_eq!(first.occurrences, 2);
        // The winding is the material's, not the identity's.
        assert_eq!(first.octet_winding, 14);
        assert_eq!(first.octets, alternating);
    }

    /// **The identity is the codec's, and declaring a different one founds a different complex.**
    ///
    /// This is the falsifier for the whole change. The same octets are admitted twice: once under a
    /// codec whose identity is the surface — which is what the organ used to hardcode — and once
    /// under a codec that declares two distinct surfaces to be one patch. If the identity were
    /// still byte equality on the surface, the two readings would be identical and this test could
    /// not fail; because it is the codec's, the second reading merges a pair the first separated,
    /// and the merge is visible as a site the material recurs at.
    #[test]
    fn declaring_a_different_patch_identity_founds_a_different_complex() {
        let by_surface = declared_patches(
            "material",
            &[(b"alpha", "alpha"), (b"beta", "beta"), (b"alpha", "alpha")],
        )
        .expect("declared patches");
        // A codec that reads both surfaces as one transformation class.
        let by_class = declared_patches(
            "material",
            &[
                (b"alpha", "class:a"),
                (b"beta", "class:a"),
                (b"alpha", "class:a"),
            ],
        )
        .expect("declared patches");

        let surface_complex =
            IncidenceComplex::found(&[by_surface], 3).expect("found under surface identity");
        assert_eq!(surface_complex.sites().len(), 2);

        // Under the coarser identity every patch is one site, so every contact is a self-contact
        // and the complex is refused for carrying no contact at all — which is the honest return:
        // a codec that collapses everything has founded no relation, and the organ says so rather
        // than returning a one-site complex that looks like a reading.
        let class_error = IncidenceComplex::found(&[by_class], 3)
            .expect_err("a total collapse founds no contact");
        assert_eq!(class_error, IncidenceProductionError::NoContact);

        // And a codec that merges exactly one pair, leaving a third apart, founds a strictly
        // coarser complex than the surface reading rather than refusing.
        let partial = declared_patches(
            "material",
            &[
                (b"alpha", "class:a"),
                (b"beta", "class:a"),
                (b"gamma", "gamma"),
            ],
        )
        .expect("declared patches");
        let partial_complex =
            IncidenceComplex::found(&[partial], 3).expect("found under the partial identity");
        assert_eq!(partial_complex.sites().len(), 2);
        assert_eq!(
            partial_complex
                .sites()
                .iter()
                .find(|site| site.surface == "class:a")
                .expect("the merged class is a site")
                .occurrences,
            2
        );
    }

    /// **The attachment is two-sided, plural, and retains both outcomes.**
    ///
    /// `H.0466` requires that a world *"admit plural upward leaders and retain connected and
    /// unconnected outcomes instead of manufacturing one ground endpoint."* This is that
    /// requirement as a check that can fail: if every attempt connected, the terrain would be a
    /// passive terminal after all; if only one did, the single endpoint would have been
    /// manufactured; and if the outcome did not follow from **both** polarities, the arrival would
    /// still be choosing where it lands.
    #[test]
    fn the_attachment_is_two_sided_and_retains_the_unconnected_attempts() {
        let base_material =
            vec![
                DeclaredOccurrence::from_text("terrain", 0, BTreeSet::new(), "alpha beta gamma")
                    .expect("declared text material"),
            ];
        let base = IncidenceComplex::found(&base_material, 8).expect("found the terrain");

        // The terrain's own chain gives one pure donor, one pure acceptor, and one of each role.
        let role = |surface: &str| {
            let at = base
                .sites()
                .iter()
                .position(|site| site.surface == surface)
                .expect("the terrain carries this constituent");
            base.site_polarity(at)
        };
        assert_eq!(role("alpha"), Some(ExposedPolarity::Donor));
        assert_eq!(role("beta"), Some(ExposedPolarity::Both));
        assert_eq!(role("gamma"), Some(ExposedPolarity::Acceptor));

        let arrival = DeclaredOccurrence::from_text("arrival", 1, BTreeSet::new(), "delta epsilon")
            .expect("declared text material");
        let response = base
            .admit_later(
                &arrival,
                PhaseChart::HalfTurnOnly,
                &CoefficientGroup::Integers,
            )
            .expect("admit the arrival");
        let attempts = response.complex.attachment(&response.trace);

        // Plural: every exposed terrain constituent reached toward every arriving one.
        assert_eq!(attempts.len(), 6);
        let connected = attempts.iter().filter(|a| a.connected).count();
        let unconnected = attempts.len() - connected;
        // BOTH outcomes are present. Neither is manufactured away.
        assert!(connected > 0, "no attempt met: the terrain is inert");
        assert!(
            unconnected > 0,
            "every attempt met: the outcome cannot vary, so it tests nothing"
        );
        assert_eq!(connected, 4);
        assert_eq!(unconnected, 2);

        // And the outcome follows from BOTH polarities, never from one side.
        for attempt in &attempts {
            let opposed = matches!(
                (attempt.terrain_polarity, attempt.arrival_polarity),
                (ExposedPolarity::Both, _)
                    | (_, ExposedPolarity::Both)
                    | (ExposedPolarity::Donor, ExposedPolarity::Acceptor)
                    | (ExposedPolarity::Acceptor, ExposedPolarity::Donor)
            );
            assert_eq!(
                attempt.connected,
                opposed,
                "{} ({:?}) → {} ({:?})",
                attempt.terrain_surface,
                attempt.terrain_polarity,
                attempt.arrival_surface,
                attempt.arrival_polarity
            );
        }

        // The two that did not meet are the same-role pairs, and each is inspectable rather than a
        // bare refusal: it carries the material's own reading of the gap it could not cross.
        for attempt in attempts.iter().filter(|a| !a.connected) {
            assert_eq!(attempt.terrain_polarity, attempt.arrival_polarity);
            assert!(attempt.contact_winding > 0);
        }
    }

    /// **The gauge check: the material moves the attachment.**
    ///
    /// A classification whose material cannot vary the property under test is the defect `CLAUDE.md`
    /// §8 convicts, wearing a passing result. Here the same arrival is met by a terrain whose own
    /// inscription gives its constituents different roles, and the outcome must move.
    #[test]
    fn changing_the_terrains_material_moves_which_attempts_meet() {
        let arrival = DeclaredOccurrence::from_text("arrival", 1, BTreeSet::new(), "delta epsilon")
            .expect("declared text material");

        let meet = |text: &str| {
            let material = vec![
                DeclaredOccurrence::from_text("terrain", 0, BTreeSet::new(), text)
                    .expect("declared text material"),
            ];
            let base = IncidenceComplex::found(&material, 8).expect("found the terrain");
            let response = base
                .admit_later(
                    &arrival,
                    PhaseChart::HalfTurnOnly,
                    &CoefficientGroup::Integers,
                )
                .expect("admit the arrival");
            let attempts = response.complex.attachment(&response.trace);
            let connected = attempts.iter().filter(|a| a.connected).count();
            (attempts.len(), connected)
        };

        // A three-constituent chain: one donor, one both, one acceptor.
        let chain = meet("alpha beta gamma");
        // A closed cycle on the same three: every constituent both donates and accepts, so every
        // attempt meets. The terrain's own material changed what the identical arrival could reach.
        let cycle = meet("alpha beta gamma alpha");
        assert_eq!(chain, (6, 4));
        assert_eq!(cycle, (6, 6));
        assert_ne!(chain.1, cycle.1);
    }

    /// The control: the text codec reproduces exactly what the organ used to do internally, so
    /// nothing above this change reads differently.
    #[test]
    fn the_text_codec_reproduces_the_previous_internal_cut() {
        let text = "the arc bends the channel";
        let occurrence =
            DeclaredOccurrence::from_text("t", 0, BTreeSet::new(), text).expect("text codec");
        let mut cut = text.split_whitespace();
        for patch in &occurrence.inscription {
            assert_eq!(Some(patch.identity()), cut.next());
            assert_eq!(patch.octets(), patch.identity().as_bytes());
        }
        assert_eq!(cut.next(), None);
        assert_eq!(occurrence.declared_surface(), text);
    }

    fn material() -> Vec<DeclaredOccurrence> {
        // A causal chain of three, whose storage ordinals deliberately do NOT ascend with it.
        vec![
            // Carries both `bends ⟶ the` and `the ⟶ bends`: the two contacts cross the same
            // number of bits (`popcount('s'⊕'t') = popcount('e'⊕'b') = 3`) and land on
            // opposed sheets (`popcount('t')` even, `popcount('b')` odd), so their transports
            // are exact inverses and the two routes through them cancel in EVERY chart.
            DeclaredOccurrence::from_text(
                "b".to_owned(),
                90,
                BTreeSet::from(["a".to_owned()]),
                "the arc bends the channel and the bends carry the return",
            )
            .expect("declared text material"),
            DeclaredOccurrence::from_text(
                "a".to_owned(),
                91,
                BTreeSet::new(),
                "the leader founds the channel and the channel carries the leader".to_owned(),
            )
            .expect("declared text material"),
            DeclaredOccurrence::from_text(
                "c".to_owned(),
                12,
                BTreeSet::from(["b".to_owned()]),
                "the channel returns the leader and the leader founds the arc".to_owned(),
            )
            .expect("declared text material"),
        ]
    }

    fn complex() -> IncidenceComplex {
        IncidenceComplex::found(&material(), 32).expect("the declared material founds a complex")
    }

    #[test]
    fn the_causal_order_is_not_the_storage_order() {
        let complex = complex();
        let ranks = complex
            .causal_ranks()
            .iter()
            .map(|(identity, ordinal, rank)| (identity.as_str(), *ordinal, *rank))
            .collect::<Vec<_>>();
        assert!(ranks.contains(&("a", 91, 0)));
        assert!(ranks.contains(&("b", 90, 1)));
        assert!(ranks.contains(&("c", 12, 2)));
        assert!(!complex.dependency_disagrees_with_storage().is_empty());
    }

    #[test]
    fn the_body_validates_partial_partial_and_storage_order_is_gauge() {
        let complex = complex();
        complex
            .validate_with_body(true)
            .expect("the body admits the complex in its indexed order");
        complex
            .validate_with_body(false)
            .expect("the body admits the same complex in another order");
        let (sorted, reversed) = complex
            .emanated_under_both_storage_orders()
            .expect("the body reads the exposed boundary");
        assert_eq!(sorted, reversed);
        assert_eq!(complex.body_outer_grain().unwrap(), 1);
    }

    #[test]
    fn a_flipped_traversal_hand_is_refused_by_the_body() {
        let complex = complex();
        assert!(!complex.compounds().is_empty());
        let refusal = complex
            .body_refuses_flipped_compound_hand(0, 0)
            .expect("the body refuses a compound whose boundary no longer telescopes");
        assert!(matches!(
            refusal,
            EventComplexError::BoundaryOfBoundary(_, _)
        ));
    }

    #[test]
    fn reversing_a_contact_hand_changes_the_composition_while_the_endpoints_hold() {
        let complex = complex();
        let bond = 0usize;
        let endpoints = (
            complex.sites()[complex.bonds()[bond].from].surface.clone(),
            complex.sites()[complex.bonds()[bond].to].surface.clone(),
        );
        let reversed = complex
            .with_reversed_bond(bond)
            .expect("reversing one hand founds a lawful complex");
        let reversed_endpoints = (
            reversed.sites()[reversed.bonds()[bond].to].surface.clone(),
            reversed.sites()[reversed.bonds()[bond].from]
                .surface
                .clone(),
        );
        assert_eq!(endpoints, reversed_endpoints);

        let source = complex.ingress()[0];
        let before = complex
            .routes_from(source, 4, PhaseChart::WindingAdjacent)
            .unwrap();
        let after = reversed
            .routes_from(source, 4, PhaseChart::WindingAdjacent)
            .unwrap();
        let moved =
            before.iter().zip(after.iter()).any(|(left, right)| {
                left.sites == right.sites && left.amplitude != right.amplitude
            }) || before.len() != after.len();
        assert!(moved, "reversing a hand left every composition unchanged");
    }

    #[test]
    fn two_routes_to_one_constituent_cancel() {
        let complex = complex();
        for chart in PhaseChart::ALL {
            let mut annihilations = 0usize;
            for source in 0..complex.sites().len() {
                let routes = complex.routes_from(source, 3, chart).unwrap();
                for target in 0..complex.sites().len() {
                    let interference = complex.interfere(&routes, target, 0);
                    if interference.cancelled {
                        // The cross term is the whole of the return: the tape reading is not zero.
                        assert!(interference.tape_reading != rat(0));
                        assert_eq!(interference.tower_reading, rat(0));
                        assert_eq!(interference.cross_term, -interference.tape_reading.clone());
                    }
                    for pair in &interference.annihilating_pairs {
                        annihilations += 1;
                        let (tape, tower, cross) = interference.pair_reading(*pair);
                        assert!(tape != rat(0));
                        assert_eq!(tower, rat(0));
                        assert_eq!(cross, -tape);
                        // The negative control: the same two currents in one mode each survive.
                        let separated = IncidenceComplex::mode_separated_population(&[
                            interference.routes[pair.0].clone(),
                            interference.routes[pair.1].clone(),
                        ]);
                        assert_eq!(separated.coherent_modes.len(), 2);
                    }
                }
            }
            assert!(
                annihilations > 0,
                "no two routes annihilated in chart {}",
                chart.name()
            );
        }
    }

    #[test]
    fn the_control_material_cannot_cancel() {
        // The falsifier must be able to fail. Every constituent distinct means the contact graph
        // is a forest: one route per arrival, so nothing can interfere with anything.
        let control = vec![DeclaredOccurrence::from_text(
            "control".to_owned(),
            0,
            BTreeSet::new(),
            "alpha bravo charlie delta echo foxtrot golf".to_owned(),
        )
        .expect("declared text material")];
        let complex = IncidenceComplex::found(&control, 32).unwrap();
        assert!(complex.compounds().is_empty());
        for chart in PhaseChart::ALL {
            for source in 0..complex.sites().len() {
                let routes = complex.routes_from(source, 4, chart).unwrap();
                for target in 0..complex.sites().len() {
                    let interference = complex.interfere(&routes, target, 0);
                    assert!(!interference.cancelled);
                    assert!(interference.annihilating_pairs.is_empty());
                }
            }
        }
    }

    #[test]
    fn a_closed_boundary_retains_holonomy_where_the_terrain_is_curved() {
        let complex = complex();
        let switched_off = complex.hand_up(PhaseChart::HalfTurnOnly).unwrap();
        let carried = complex.hand_up(PhaseChart::WindingAdjacent).unwrap();
        assert_eq!(switched_off.len(), carried.len());
        assert!(!carried.is_empty());
        assert!(
            carried.iter().any(|emission| !emission.terrain_is_flat()),
            "every closed boundary returned the identity"
        );
        // The rotation switched off can only ever return the identity: that is the tape's chart,
        // and it is why a tape cannot see curvature.
        assert!(switched_off
            .iter()
            .all(|emission| emission.terrain_is_flat()));
        // The chart is a gauge and must act non-trivially, or it is not a gauge (`CLAUDE.md` §8).
        assert!(switched_off
            .iter()
            .zip(carried.iter())
            .any(|(left, right)| left.holonomy != right.holonomy));
    }

    #[test]
    fn the_holonomy_does_not_depend_on_which_way_the_boundary_is_walked() {
        // Reversing a closed boundary inverts its transport, so flatness is a property of the
        // compound. A chain gauge promoted into the invariant would flip on odd boundaries; this
        // is the check that it was not.
        let complex = complex();
        for at in 0..complex.compounds().len() {
            let (_, forward) = complex.holonomy(at, PhaseChart::WindingSpread).unwrap();
            let reverse = forward.inverse();
            assert_eq!(
                forward == ExactWavePhaseTransport::identity(),
                reverse == ExactWavePhaseTransport::identity()
            );
        }
    }

    #[test]
    fn a_flat_closed_boundary_is_reachable() {
        // The falsifier must be able to fail. `ab ⟷ cc` crosses one bit each way — equal turning
        // magnitude — and lands on opposed sheets, because `popcount('c')` is even and
        // `popcount('a')` is odd. The two turns are exact inverses and the boundary returns the
        // identity while neither turn is the identity. So `curved` is a measurement of the
        // material and not a property of the chart.
        let material = vec![DeclaredOccurrence::from_text(
            "flat".to_owned(),
            0,
            BTreeSet::new(),
            "ab cc ab".to_owned(),
        )
        .expect("declared text material")];
        let complex = IncidenceComplex::found(&material, 8).unwrap();
        let emissions = complex.hand_up(PhaseChart::WindingAdjacent).unwrap();
        assert!(!emissions.is_empty());
        assert!(
            emissions.iter().any(|emission| emission.terrain_is_flat()),
            "no closed boundary on the declared flat material returned the identity"
        );
        // And the turns that cancelled were not themselves the identity: a boundary of identities
        // would prove nothing.
        assert!(complex.bonds().iter().all(|bond| bond.contact_winding != 0));
    }

    #[test]
    fn a_completed_compound_emits_one_successor_with_its_residual() {
        let complex = complex();
        let emissions = complex.hand_up(PhaseChart::WindingAdjacent).unwrap();
        assert_eq!(emissions.len(), complex.compounds().len());
        for emission in &emissions {
            assert_eq!(emission.grain, 1);
            assert!(!emission.surface.is_empty());
            assert!(emission.residual.internal_contacts >= 2);
        }
        if let Ok((handed, next)) = complex.next_grain(PhaseChart::WindingAdjacent) {
            assert_eq!(handed, emissions);
            assert_eq!(next.grain(), 1);
            next.validate_with_body(true)
                .expect("the body admits the grain-one complex");
            // A grain-one contact is an actual contact of the grain-zero complex crossing between
            // two closed boundaries, so it can never exceed the contact population below it.
            assert!(next.bonds().len() <= complex.bonds().len());
            assert!(
                next.bonds()
                    .iter()
                    .all(|bond| !bond.contact_faces.is_empty()),
                "a higher-grain contact erased every lower contact face"
            );
        }
    }

    // ------------------------------------------------------------------------------------
    // Differentiation, and the response to later material
    // ------------------------------------------------------------------------------------

    #[test]
    fn the_engine_admits_the_same_complex_the_body_admits() {
        let complex = complex();
        complex.validate_with_body(true).expect("the body admits");
        let view = complex.engine_view().expect("the engine admits");
        let f_vector = view.complex().f_vector();
        assert_eq!(f_vector.get(&0).copied(), Some(complex.sites().len()));
        assert_eq!(f_vector.get(&1).copied(), Some(complex.bonds().len()));
        assert_eq!(f_vector.get(&2).copied(), Some(complex.compounds().len()));
    }

    #[test]
    fn stokes_holds_on_every_closed_boundary() {
        let complex = complex();
        let differentiated = complex
            .differentiate_all(PhaseChart::WindingAdjacent)
            .unwrap();
        assert!(!differentiated.is_empty());
        for one in &differentiated {
            assert!(
                one.stokes_holds(),
                "⟨w, ∂Σ⟩ = {} against ⟨dw, Σ⟩ = {} on {:?}",
                one.residual,
                one.coboundary_reading,
                one.surface
            );
        }
        // The falsifier must be able to fail: some closed boundary must carry a non-zero residual,
        // or the identity is being checked on `0 = 0` everywhere.
        assert!(differentiated
            .iter()
            .any(|one| one.residual != BigInt::from(0)));
    }

    #[test]
    fn differentiation_returns_exactly_what_closure_departed() {
        let complex = complex();
        let chart = PhaseChart::WindingAdjacent;
        let emissions = complex.hand_up(chart).unwrap();
        let differentiated = complex.differentiate_all(chart).unwrap();
        assert_eq!(emissions.len(), differentiated.len());
        for (emission, one) in emissions.iter().zip(differentiated.iter()) {
            let departed = emission
                .residual
                .departed_contacts
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            let restored = one
                .reexposed
                .iter()
                .map(|contact| format!("{} ⟶ {}", contact.from, contact.to))
                .collect::<BTreeSet<_>>();
            assert_eq!(departed, restored, "on {:?}", one.surface);
        }
    }

    #[test]
    fn the_two_cycle_bases_agree_on_the_image_of_the_holonomy_homomorphism() {
        // The bases differ — this module's fundamental cycles and `found_potential_in`'s spanning
        // forest are built independently — so what must agree is the subgroup of ℤ they generate,
        // never the basis. A basis is a receiver-visible coordinate.
        let complex = complex();
        let group = CoefficientGroup::Integers;
        let chords = complex.chord_population(&group).unwrap();
        let module = complex.holonomy_image(PhaseChart::WindingAdjacent).unwrap();
        assert_eq!(chords.cycle_rank, complex.compounds().len());
        assert_eq!(module, chords.image);
        assert_ne!(module, BigInt::from(0));
    }

    #[test]
    fn the_residual_of_a_combination_is_linear() {
        let complex = complex();
        let differentiated = complex
            .differentiate_all(PhaseChart::WindingAdjacent)
            .unwrap();
        assert!(differentiated.len() >= 2);
        for left in 0..differentiated.len() {
            for right in (left + 1)..differentiated.len() {
                let difference = complex
                    .residual_of_combination(&[(left, 1), (right, -1)])
                    .unwrap();
                assert_eq!(
                    difference,
                    &differentiated[left].residual - &differentiated[right].residual
                );
            }
        }
    }

    #[test]
    fn a_later_arrival_changes_a_named_earlier_compound() {
        let complex = complex();
        let chart = PhaseChart::WindingAdjacent;
        let group = CoefficientGroup::Integers;
        let arrival = DeclaredOccurrence::from_text(
            "arrival".to_owned(),
            7,
            BTreeSet::from(["a".to_owned()]),
            "the bends carry arc the".to_owned(),
        )
        .expect("declared text material");
        let response = complex.admit_later(&arrival, chart, &group).unwrap();
        assert!(response.arrival_is_co_present);
        assert_eq!(response.arrival_rank, 1);
        assert!(!response.reached.is_empty());
        assert!(!response.reopened.is_empty());
        assert!(!response.saturated.is_empty());
        assert!(!response.untouched.is_empty());

        // A closed boundary is permanent: adding cells to a graph never destroys a cycle. This is
        // a theorem and it is checked rather than assumed.
        assert!(response.no_closed_boundary_moved());
        assert!(response.dissolved.is_empty());
        // And the region grew: closed boundaries exist that did not before.
        assert!(!response.founded.is_empty());
        // What DID move on a named standing compound is its valence, and the law predicts it
        // exactly.
        assert!(response
            .verdicts
            .iter()
            .any(|verdict| verdict.valence_moved));
        let (right, wrong) = response.valence_law_agreement();
        assert_eq!(wrong, 0, "the valence law was wrong {wrong} times");
        assert_eq!(right, response.verdicts.len());
    }

    #[test]
    fn withdrawing_the_arrival_restores_the_original_bit_exactly() {
        let complex = complex();
        let chart = PhaseChart::WindingAdjacent;
        let group = CoefficientGroup::Integers;
        let arrival = DeclaredOccurrence::from_text(
            "arrival".to_owned(),
            7,
            BTreeSet::from(["a".to_owned()]),
            "the bends carry arc the".to_owned(),
        )
        .expect("declared text material");
        let response = complex.admit_later(&arrival, chart, &group).unwrap();
        assert_ne!(response.before, response.after);
        let withdrawn = response.complex.withdraw(&response.trace).unwrap();
        assert_eq!(withdrawn.sites().len(), complex.sites().len());
        assert_eq!(withdrawn.bonds().len(), complex.bonds().len());
        assert_eq!(withdrawn.hand_up(chart).unwrap(), response.before);
        // The withdrawal is an inverse on the admitted complex, so a retained multiplicity would
        // show up here and nowhere else.
        assert!(!response.trace.bond_multiplicity_delta.is_empty());
        for (at, delta) in &response.trace.bond_multiplicity_delta {
            assert_eq!(
                withdrawn.bonds()[*at].multiplicity + delta,
                response.complex.bonds()[*at].multiplicity
            );
        }
    }

    #[test]
    fn a_saturated_compound_is_reached_and_hands_forward_nothing() {
        // The control: the closed boundary's residual is exactly zero, the arrival reaches it with
        // genuinely new cells, and the cycle it founds through the compound carries the compound's
        // whole contribution — which is nothing.
        let material = vec![DeclaredOccurrence::from_text(
            "saturated".to_owned(),
            0,
            BTreeSet::new(),
            "ab cc ab".to_owned(),
        )
        .expect("declared text material")];
        let complex = IncidenceComplex::found(&material, 8).unwrap();
        let chart = PhaseChart::WindingAdjacent;
        let group = CoefficientGroup::Integers;
        let differentiated = complex.differentiate_all(chart).unwrap();
        assert_eq!(differentiated.len(), 1);
        assert_eq!(differentiated[0].residual, BigInt::from(0));
        assert!(differentiated[0].holonomy_is_flat());
        assert!(differentiated[0].is_saturated(&group));

        let arrival = DeclaredOccurrence::from_text(
            "saturated:arrival".to_owned(),
            1,
            BTreeSet::new(),
            "ab ee cc ab".to_owned(),
        )
        .expect("declared text material");
        let response = complex.admit_later(&arrival, chart, &group).unwrap();
        assert_eq!(response.reached.len(), 1);
        assert!(
            response.reopened.is_empty(),
            "a saturated compound reopened"
        );
        assert_eq!(response.saturated.len(), 1);
        assert!(response.no_closed_boundary_moved());

        // The transport half: `r(Σ' − Σ) = r(Σ') − 0 = r(Σ')`, with `r(Σ')` non-zero so the
        // statement is visible rather than `0 = 0`.
        let admitted = response.complex.differentiate_all(chart).unwrap();
        let standing = admitted
            .iter()
            .position(|one| one.residual == BigInt::from(0))
            .expect("the saturated compound survives");
        let founded = admitted
            .iter()
            .position(|one| one.residual != BigInt::from(0))
            .expect("the arrival founded a cycle with a residual");
        let difference = response
            .complex
            .residual_of_combination(&[(founded, 1), (standing, -1)])
            .unwrap();
        assert_eq!(difference, admitted[founded].residual);
        assert_ne!(difference, BigInt::from(0));
    }

    #[test]
    fn the_causally_later_arrival_reaches_only_along_the_dependency_relation() {
        let complex = complex();
        let chart = PhaseChart::WindingAdjacent;
        let group = CoefficientGroup::Integers;
        let arrival = DeclaredOccurrence::from_text(
            "later".to_owned(),
            400,
            BTreeSet::from(["c".to_owned()]),
            "the channel returns the arc".to_owned(),
        )
        .expect("declared text material");
        let response = complex.admit_later(&arrival, chart, &group).unwrap();
        assert!(!response.arrival_is_co_present);
        assert_eq!(response.arrival_rank, 3);
        assert!(response.new_dependencies > 0, "no ⪯ edge reached back");
        assert!(response.no_closed_boundary_moved());
        assert!(response
            .verdicts
            .iter()
            .any(|verdict| verdict.valence_moved));
        let (_, wrong) = response.valence_law_agreement();
        assert_eq!(wrong, 0);
    }

    #[test]
    fn an_arrival_naming_a_cause_outside_the_family_is_refused() {
        let complex = complex();
        let arrival = DeclaredOccurrence::from_text(
            "orphan".to_owned(),
            0,
            BTreeSet::from(["not-in-the-family".to_owned()]),
            "the leader".to_owned(),
        )
        .expect("declared text material");
        assert!(matches!(
            complex.arrival_rank(&arrival),
            Err(IncidenceProductionError::ArrivalCauseIsOutsideTheFamily(_))
        ));
    }

    #[test]
    fn the_causal_rank_guard_refuses_nothing_the_boundaries_would_have_admitted() {
        // The tower's ceiling is not the `⪯` guard on this material, and that is a measurement
        // rather than an assumption. `would_bond_across_rank` is the counterfactual: pairs the
        // guard refused before looking, which the boundary test would have admitted.
        let complex = complex();
        let census = complex.next_grain_census();
        assert!(census.refused_by_causal_rank > 0, "the guard never fired");
        assert_eq!(census.would_bond_across_rank, 0);
        assert_eq!(
            census.same_rank + census.refused_by_causal_rank,
            census.pairs_considered
        );
        assert_eq!(census.bonded + census.refused_unbonded, census.same_rank);
    }

    #[test]
    fn every_declared_chart_stays_on_the_exact_unit_conic() {
        for chart in PhaseChart::ALL {
            for winding in 0..24u32 {
                assert!(chart.rotation(winding).unwrap().is_unit());
            }
        }
    }
}
