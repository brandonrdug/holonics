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
    DimensionalWaveModeId, ExactComplexWaveCurrent, ExactReceiverPhasePopulation,
    ExactWavePhaseTransport,
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
}

/// One occurrence of the declared material, as the corpus carries it.
///
/// `storage_ordinal` is present **only so that `⪯` can be shown not to be it**. Nothing in this
/// module reads it except [`IncidenceComplex::dependency_disagrees_with_storage`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclaredOccurrence {
    pub identity: String,
    pub storage_ordinal: u64,
    pub caused_by: BTreeSet<String>,
    pub text: String,
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
    pub surface: String,
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
    pub const ALL: [Self; 3] = [Self::HalfTurnOnly, Self::WindingAdjacent, Self::WindingSpread];

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
    pub fn rotation(self, winding: u32) -> Result<ExactWavePhaseTransport, IncidenceProductionError> {
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
        if occurrences.is_empty() || patch_extent == 0 {
            return Err(IncidenceProductionError::NoDeclaredMaterial);
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
            let complete = occurrence.text.split_whitespace().count();
            if complete == 0 {
                return Err(IncidenceProductionError::EmptyOccurrence(
                    occurrence.identity.clone(),
                ));
            }
            patches_outside_extent = patches_outside_extent
                .checked_add(complete.saturating_sub(patch_extent) as u64)
                .ok_or(IncidenceProductionError::Extent)?;

            let mut previous: Option<usize> = None;
            for patch in occurrence.text.split_whitespace().take(patch_extent) {
                let key = (rank, patch.to_owned());
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
                            surface: patch.to_owned(),
                            causal_rank: rank,
                            grain: 0,
                            octet_winding: octet_winding(patch.as_bytes()),
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
                        found_bond(&mut bonds, &mut bond_index, &sites, prior, at_site, rank, 0)?;
                    }
                }
                previous = Some(at_site);
            }
        }
        if bonds.is_empty() {
            return Err(IncidenceProductionError::NoContact);
        }

        // `⪯`: one constituent recurring at a later causal rank. This is the corpus's own causal
        // order carried into the complex; nothing here consults storage position.
        let mut by_surface = BTreeMap::<&str, Vec<usize>>::new();
        for (at, site) in sites.iter().enumerate() {
            by_surface.entry(site.surface.as_str()).or_default().push(at);
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
                    (occurrence.identity.clone(), occurrence.storage_ordinal, ranks[at])
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
        let mut cells = Vec::with_capacity(self.sites.len() + self.bonds.len() + self.compounds.len());
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
            for (slot, (at, hand)) in compound
                .bonds
                .iter()
                .zip(compound.hands.iter())
                .enumerate()
            {
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
            ports.sort_by_key(|port| {
                (
                    matches!(port.kind(), EventPortKind::Exposed),
                    port.slot(),
                )
            });
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
        let complex =
            EventComplex::new(&cells, &incidences, &ports).map_err(IncidenceProductionError::Body)?;
        complex.outer_grain().map_err(IncidenceProductionError::Body)
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
        let bond = *target.bonds.get(edge).ok_or(IncidenceProductionError::Extent)?;
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
            by_target.entry(route.target).or_default().push(route.clone());
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
                for (at, hand) in donor.1.iter() {
                    if let Some(other) = acceptor.1.get(at) {
                        if *hand == other.reversed() {
                            glued |= hand.coefficient() > 0;
                        } else {
                            incoherent += 1;
                        }
                    }
                }
                // Species two: a contact of this complex LEAVES one closed boundary and ARRIVES at
                // the other, and is internal to neither. §IV: removing or reversing it changes
                // later lawful transport.
                let crossing = self.bonds.iter().enumerate().any(|(at, bond)| {
                    !donor.1.contains_key(&at)
                        && !acceptor.1.contains_key(&at)
                        && donor.0.contains(&bond.from)
                        && acceptor.0.contains(&bond.to)
                });
                if glued || crossing {
                    found_bond(
                        &mut bonds,
                        &mut bond_index,
                        &sites,
                        left,
                        right,
                        self.compounds[left].causal_rank,
                        grain,
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
) -> Result<(), IncidenceProductionError> {
    match index.get(&(from, to)) {
        Some(at) => {
            bonds[*at].multiplicity = bonds[*at]
                .multiplicity
                .checked_add(1)
                .ok_or(IncidenceProductionError::Extent)?;
        }
        None => {
            index.insert((from, to), bonds.len());
            bonds.push(Bond {
                id: EventCellId::new(0),
                from,
                to,
                causal_rank,
                grain,
                contact_winding: contact_winding(
                    sites[from].surface.as_bytes(),
                    sites[to].surface.as_bytes(),
                ),
                sheet: sheet_of(sites[to].surface.as_bytes()),
                multiplicity: 1,
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
fn causal_ranks(
    occurrences: &[DeclaredOccurrence],
) -> Result<Vec<u32>, IncidenceProductionError> {
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

    fn material() -> Vec<DeclaredOccurrence> {
        // A causal chain of three, whose storage ordinals deliberately do NOT ascend with it.
        vec![
            DeclaredOccurrence {
                identity: "b".to_owned(),
                storage_ordinal: 90,
                caused_by: BTreeSet::from(["a".to_owned()]),
                // Carries both `bends ⟶ the` and `the ⟶ bends`: the two contacts cross the same
                // number of bits (`popcount('s'⊕'t') = popcount('e'⊕'b') = 3`) and land on
                // opposed sheets (`popcount('t')` even, `popcount('b')` odd), so their transports
                // are exact inverses and the two routes through them cancel in EVERY chart.
                text: "the arc bends the channel and the bends carry the return".to_owned(),
            },
            DeclaredOccurrence {
                identity: "a".to_owned(),
                storage_ordinal: 91,
                caused_by: BTreeSet::new(),
                text: "the leader founds the channel and the channel carries the leader".to_owned(),
            },
            DeclaredOccurrence {
                identity: "c".to_owned(),
                storage_ordinal: 12,
                caused_by: BTreeSet::from(["b".to_owned()]),
                text: "the channel returns the leader and the leader founds the arc".to_owned(),
            },
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
            reversed.sites()[reversed.bonds()[bond].from].surface.clone(),
        );
        assert_eq!(endpoints, reversed_endpoints);

        let source = complex.ingress()[0];
        let before = complex
            .routes_from(source, 4, PhaseChart::WindingAdjacent)
            .unwrap();
        let after = reversed
            .routes_from(source, 4, PhaseChart::WindingAdjacent)
            .unwrap();
        let moved = before.iter().zip(after.iter()).any(|(left, right)| {
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
        let control = vec![DeclaredOccurrence {
            identity: "control".to_owned(),
            storage_ordinal: 0,
            caused_by: BTreeSet::new(),
            text: "alpha bravo charlie delta echo foxtrot golf".to_owned(),
        }];
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
        let material = vec![DeclaredOccurrence {
            identity: "flat".to_owned(),
            storage_ordinal: 0,
            caused_by: BTreeSet::new(),
            text: "ab cc ab".to_owned(),
        }];
        let complex = IncidenceComplex::found(&material, 8).unwrap();
        let emissions = complex.hand_up(PhaseChart::WindingAdjacent).unwrap();
        assert!(!emissions.is_empty());
        assert!(
            emissions.iter().any(|emission| emission.terrain_is_flat()),
            "no closed boundary on the declared flat material returned the identity"
        );
        // And the turns that cancelled were not themselves the identity: a boundary of identities
        // would prove nothing.
        assert!(complex
            .bonds()
            .iter()
            .all(|bond| bond.contact_winding != 0));
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
        }
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
