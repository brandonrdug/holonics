//! The adapter from an exact physical contact complex to the engine's graded chain complex.
//!
//! [`crate::physical_constraint_complex::PhysicalConstraintComplex`] founds incidence from an
//! exact squared-distance interval compared against a declared aperture. That classification is a
//! **trichotomy**, not a predicate: `D.upper <= a` is `Inside`, `D.lower > a` is `Outside`, and
//! every interval that straddles the aperture stays `Open`. A graded chain complex, on the other
//! hand, wants a definite incidence — a 1-cell either exists or it does not, and
//! [`GradedCausalComplex::found_cell`] has no third answer.
//!
//! # The law this adapter applies to the open class
//!
//! [definition] **An open contact is not decided here and is never silently decided anywhere.**
//! The adapter does not return one complex. It returns a *family*
//! ([`ConstraintComplexFamily`]) indexed by the resolutions of the open set, together with the
//! open set itself — each open contact retained with its exact interval, its aperture and its
//! addressed pair. A member of that family ([`GradedConstraintComplex`]) always carries the
//! [`OpenResolution`] that produced it, so no complex leaving this module can be read without
//! reading which open contacts it admitted.
//!
//! The family's cardinality is exactly `2^n` for `n` open contacts. Two members are always
//! constructed because they bound the family in the inclusion order of 1-cells:
//!
//! - [`ConstraintComplexFamily::refusing`] — every open contact refused. This member, and only
//!   this member, reproduces the incidence the presented complex already carries: its 1-cells are
//!   `polygonal_edges ∪ contact_edges` and its 2-cells are exactly `faces`. It is *one member*,
//!   not the answer.
//! - [`ConstraintComplexFamily::admitting`] — every open contact founded.
//!
//! [definition] Any other member is built by naming its resolution:
//! [`graded_constraint_member`] with [`OpenContactLaw::Declared`], which refuses unless the
//! resolution names **every** open contact exactly once and names nothing else. There is no
//! default, no majority rule and no fallthrough. Enumerating the whole family is
//! [`enumerate_family`], which takes an explicit bound and returns
//! [`ConstraintGradingError::OpenFamilyTooWide`] rather than silently exponentiating.
//!
//! An open contact whose canonical edge is *also* carried `Inside` by some other aperture is not
//! open as an incidence question — the 1-cell exists. Those are removed from the open set and
//! retained by name in [`ConstraintComplexFamily::open_subsumed_by_inside`]; nothing is dropped
//! quietly.
//!
//! # Which families this adapter reads
//!
//! [definition] Both. It walks `PhysicalConstraintComplex::contact_families` and asks each reading
//! for its class, so a [`crate::physical_constraint_complex::ContactFamilyKind::WithinComponent`]
//! family — the intra-chain contacts of one presented chain, at a declared sequence separation —
//! reaches every member, every open resolution and every consumer of this adapter through exactly
//! the path a cross family reaches them by. The one thing the diagonal changes is the 2-cell law:
//! a junction that coincides with its own chain step's endpoint founds no triangle and is skipped.
//!
//! The covalent chain steps are [`EdgeProvenance::Polygonal`] and stand in every member
//! unconditionally, so a within-component contact `(i, j)` closes the chain segment between its
//! endpoints into a 1-cycle of `j − i + 1` one-cells in every member that admits it. The Lean
//! owner proves that cycle is a cycle, that it is not a boundary of nothing, and that it spans the
//! whole cycle module of the segment (`backboneContactCycle_is_cycle`,
//! `segment_cycles_are_multiples`).
//!
//! # Why `∂∘∂ = 0` holds for every member
//!
//! [proved-derived; implemented-exact] Unconditionally, and independently of the open set. A
//! 2-cell is founded only on three distinct vertices `[a,b,c]` — a degenerate triple is refused by
//! name with [`ConstraintGradingError::DegenerateFace`], and the Lean owner shows the identity
//! does not even need that — with all three of its 1-faces already founded, and
//! [`crate::physical_constraint_complex::ConstraintFace::boundary`] supplies the alternating
//! `∂[a,b,c] = [b,c] − [a,c] + [a,b]`. Each 1-cell's boundary is `[upper] − [lower]`, and the
//! hand `ConstraintEdge::new` returns makes `hand · ∂(canonical edge) = [second] − [first]` for
//! the presented order. So
//!
//! ```text
//! ∂∂[a,b,c] = ([c] − [b]) − ([c] − [a]) + ([b] − [a]) = 0
//! ```
//!
//! telescopes with no hypothesis on the aperture, the interval or the resolution. A resolution
//! changes **which** cells exist; it never changes the algebra of the cells that do. The founding
//! condition — a 2-cell exists only when its three 1-faces exist — is what keeps the 2-cell
//! population closed, and it is enforced by construction for every resolution because the
//! condition is stated on the resolved edge set itself. `found_cell` re-derives the identity at
//! every founding, so the claim is checked and not asserted.
//!
//! # Formal owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/AperturedGradedComplex.lean`,
//! namespace `Soma.Holonics.Foundation.AperturedGradedComplex`. The correspondence, both
//! directions:
//!
//! | Rust | Lean |
//! |---|---|
//! | `algebraic::GradedCausalComplex` + `found_cell`'s three checks | `GradedComplex` (`grade`, `boundary`, `boundary_grade`, `ground_has_no_boundary`) |
//! | `GradedCausalComplex::boundary_of_chain` | `GradedComplex.d` |
//! | `found_cell`'s `BoundarySquaredNonzero` refusal | `BoundarySquaresToZero`, lifted by `d_comp_d` / `d_d_apply` |
//! | `physical_constraint_complex::DistanceAperture::classify` | `classify` with `classify_eq_{inside,outside,openContact}_iff` |
//! | `ContactClass::Open` is never produced by a point position | `classify_point_ne_openContact` |
//! | [`OpenResolution`] | `Resolution` |
//! | [`OpenContactLaw`] applied to a reading | `admits` |
//! | an `Inside`/`Outside` reading is unmoved by any resolution | `decided_admission_is_resolution_free` |
//! | the return is a *family*, not a complex | `openContact_is_plural` |
//! | [`ConstraintComplexFamily::is_determinate`] | `determinate_of_no_openContact` |
//! | `ConstraintFace::boundary`'s alternating hand | `cellBoundary` on `ConstraintCell.face`, `orientedEdge` |
//! | `∂∘∂ = 0` for every member | `constraint_boundary_squared`, `constraint_d_comp_d` |
//! | the 2-cell founding law replayed in `found_member` | `FaceStands`, `founded_face_boundary_stands` |
//! | the whole adapter contract | `adapter_contract` |
//!
//! Every one of those elaborates with no `sorryAx`.
//!
//! # What the family reaches
//!
//! Every member is an ordinary [`GradedCausalComplex`], so the engine's existing exact receivers
//! consume it unchanged: `rebase_invariants` for Betti numbers with torsion through Smith normal
//! form, `sheaf_diffusion::ExactCellularSheaf` for the coboundary and the exact Hodge Laplacian
//! `Δ_k = δ_{k−1}δ_{k−1}ᵀ + δ_kᵀδ_k`, and `lattice_gauge::exact_spectrum` for that operator's
//! exact spectrum. No float decides an incidence, a rank or an eigenvalue anywhere on that path.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::EventId;
use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::exact_value::ExactInterval;
use crate::physical_constraint_complex::{
    ConstraintComponentId, ConstraintEdge, ConstraintError, ConstraintFace, ConstraintFaceId,
    ConstraintVertexId, ContactClass, PhysicalConstraintComplex,
};

/// Why a 1-cell exists. An admitted contact and a *resolved* open contact are different
/// provenances and are never merged: the second one exists by a declared choice.
///
/// [definition] There are two species here, not three. [`Self::Polygonal`] is the **covalent**
/// class — a step of the presented chain, founded by the presentation itself and standing in
/// *every* member of the family whatever the aperture or the resolution says. The other two are
/// **contact** classes, which exist because a squared-distance interval was compared against an
/// aperture. [`Self::is_covalent_backbone`] and [`Self::is_contact`] name that split, and it is
/// what makes a loop closed by one contact over a chain segment a genuine 1-cycle of every
/// member: the segment's 1-cells are already there.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum EdgeProvenance {
    /// A step of a presented component's own polygonal chain — the covalent backbone class.
    /// Founded by [`PhysicalConstraintComplex::found`] and unaffected by any aperture, any
    /// contact family and any resolution.
    Polygonal,
    /// A contact whose exact squared-distance interval lies at or below its aperture.
    AdmittedContact,
    /// A contact whose exact interval straddles its aperture, founded by this member's declared
    /// resolution.
    ResolvedOpenContact,
}

impl EdgeProvenance {
    /// Whether this 1-cell is a covalent step of a presented chain rather than a contact.
    ///
    /// A within-component contact family never produces one: its declared sequence separation is
    /// at least `2`, so the covalent pairs are excluded from it by
    /// [`crate::physical_constraint_complex::ConstraintError::SeparationIsCovalent`], and a pair
    /// that is both a chain step and an admitted contact resolves here to `Polygonal` because the
    /// covalent bond is why the 1-cell stands.
    pub const fn is_covalent_backbone(self) -> bool {
        matches!(self, Self::Polygonal)
    }

    /// Whether this 1-cell exists because an exact interval was compared against an aperture.
    pub const fn is_contact(self) -> bool {
        !self.is_covalent_backbone()
    }
}

/// One contact whose exact squared-distance interval straddles its aperture.
///
/// Everything needed to re-decide it later is retained: the addressed pair, the aperture that
/// could not decide it, and the interval itself.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenContact {
    pub edge: ConstraintEdge,
    pub left: ConstraintVertexId,
    pub right: ConstraintVertexId,
    pub left_component: ConstraintComponentId,
    pub right_component: ConstraintComponentId,
    pub left_ordinal: u32,
    pub right_ordinal: u32,
    pub aperture_lineage: String,
    pub aperture_squared: Rat,
    pub squared_distance: ExactInterval,
}

/// A declared disposition of every open contact: `true` founds its 1-cell, `false` refuses it.
///
/// There is deliberately no third value here. The open class is carried by the *family*, not by a
/// third incidence state smuggled into a chain complex that cannot hold one.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenResolution {
    admitted: BTreeMap<ConstraintEdge, bool>,
}

impl OpenResolution {
    pub fn declared(admitted: impl IntoIterator<Item = (ConstraintEdge, bool)>) -> Self {
        Self {
            admitted: admitted.into_iter().collect(),
        }
    }

    pub fn dispositions(&self) -> &BTreeMap<ConstraintEdge, bool> {
        &self.admitted
    }

    pub fn is_admitted(&self, edge: &ConstraintEdge) -> bool {
        self.admitted.get(edge).copied().unwrap_or(false)
    }

    pub fn admitted_edges(&self) -> Vec<ConstraintEdge> {
        self.admitted
            .iter()
            .filter(|(_, admitted)| **admitted)
            .map(|(edge, _)| *edge)
            .collect()
    }

    pub fn refused_edges(&self) -> Vec<ConstraintEdge> {
        self.admitted
            .iter()
            .filter(|(_, admitted)| !**admitted)
            .map(|(edge, _)| *edge)
            .collect()
    }

    pub fn open_count(&self) -> usize {
        self.admitted.len()
    }
}

/// The law this adapter applies to the open class of one presentation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OpenContactLaw {
    /// Refuse every open contact. The member whose incidence equals the presented complex's own.
    RefuseEveryOpen,
    /// Found every open contact. The opposite bound of the family.
    AdmitEveryOpen,
    /// A per-contact choice. Refused unless it names every open contact exactly once and names
    /// nothing that is not open.
    Declared(OpenResolution),
}

/// One member of the family: a graded chain complex together with the resolution that produced it.
/// A remounted member can validate its internal algebraic/map coherence through
/// [`Self::validate_structure`]; that check deliberately cannot reconstruct the original physical
/// contact presentation from this aggregate receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradedConstraintComplex {
    pub schema: String,
    pub presentation_lineage: String,
    pub source_event: EventId,
    /// The disposition of every open contact of the presentation. Empty exactly when the
    /// presentation carries no open contact, in which case the family is a singleton.
    pub resolution: OpenResolution,
    pub complex: GradedCausalComplex,
    pub vertex_cells: BTreeMap<ConstraintVertexId, CausalCellId>,
    pub edge_cells: BTreeMap<ConstraintEdge, CausalCellId>,
    pub edge_provenance: BTreeMap<ConstraintEdge, EdgeProvenance>,
    pub face_cells: BTreeMap<[ConstraintVertexId; 3], CausalCellId>,
}

impl GradedConstraintComplex {
    /// [definition] **The incidence as the core complex `K`** (plan phase 4): one member of the constraint family. A presented `PhysicalConstraintComplex` with open
    /// contacts is a family of core complexes, one per resolution, never one.
    /// The chart reads the carried [`crate::GradedCausalComplex`] through
    /// [`crate::GradedCausalComplex::core_chart`]; this type's other fields stay on the engine
    /// presentation.
    pub fn core_chart(
        &self,
    ) -> Result<crate::algebraic::CoreCellChart, crate::algebraic::CoreChartRefusal> {
        self.complex.core_chart()
    }

    /// Validate the structural coherence needed by downstream Hodge/rigidity consumers.
    ///
    /// This checks the remounted report's own algebraic carrier and maps; it does not claim to
    /// reconstruct the original physical contact presentation or prove that the report came from
    /// `found_member`.
    pub fn validate_structure(&self) -> Result<(), ConstraintGradingError> {
        if self.schema != "holonic-engine.graded-constraint-complex.v1" {
            return Err(ConstraintGradingError::MemberInvariant(
                "graded-complex schema disagrees".to_owned(),
            ));
        }
        self.complex.validate()?;
        if self.edge_cells.keys().ne(self.edge_provenance.keys()) {
            // Preserve the existing named orphan refusal when applicable.
            if let Some(edge) = self.edge_provenance.keys().find(|e| !self.edge_cells.contains_key(e)) {
                return Err(ConstraintGradingError::ProvenanceWithoutCell(*edge));
            }
            return Err(ConstraintGradingError::MemberInvariant(
                "an edge cell has no provenance".to_owned(),
            ));
        }
        let mut mapped = BTreeSet::new();
        for cell in self.vertex_cells.values().chain(self.edge_cells.values()).chain(self.face_cells.values()) {
            if !mapped.insert(*cell) {
                return Err(ConstraintGradingError::MemberInvariant(
                    "distinct mapped objects share one cell".to_owned(),
                ));
            }
        }
        if mapped != self.complex.cells().keys().copied().collect() {
            return Err(ConstraintGradingError::MemberInvariant(
                "object maps do not cover exactly the complex's cells".to_owned(),
            ));
        }
        for (vertex, cell_id) in &self.vertex_cells {
            let cell = self.complex.cell(*cell_id)?;
            if cell.grade != 0 || !cell.boundary.is_zero() {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "vertex {vertex:?} does not map to a boundary-free grade-zero cell"
                )));
            }
        }
        for (edge, cell_id) in &self.edge_cells {
            let cell = self.complex.cell(*cell_id)?;
            if cell.grade != 1 {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "edge {edge:?} maps to grade {}",
                    cell.grade
                )));
            }
            let lower = self.vertex_cells.get(&edge.lower).ok_or_else(|| {
                ConstraintGradingError::MemberInvariant(format!(
                    "edge {edge:?} has no lower vertex cell"
                ))
            })?;
            let upper = self.vertex_cells.get(&edge.upper).ok_or_else(|| {
                ConstraintGradingError::MemberInvariant(format!(
                    "edge {edge:?} has no upper vertex cell"
                ))
            })?;
            let mut expected = CausalChain::default();
            expected.add_term(*upper, ComparativeMultiplicity::positive(1_u8));
            expected.add_term(*lower, ComparativeMultiplicity::negative(1_u8));
            if cell.boundary != expected {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "edge {edge:?} boundary disagrees with its vertex cells"
                )));
            }
        }
        for (edge, provenance) in &self.edge_provenance {
            if !self.edge_cells.contains_key(edge) {
                return Err(ConstraintGradingError::ProvenanceWithoutCell(*edge));
            }
            if *provenance == EdgeProvenance::ResolvedOpenContact
                && !self.resolution.dispositions().get(edge).copied().unwrap_or(false)
            {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "resolved-open edge {edge:?} is not admitted by the resolution"
                )));
            }
        }
        for (edge, admitted) in self.resolution.dispositions() {
            if *admitted
                && self.edge_provenance.get(edge) != Some(&EdgeProvenance::ResolvedOpenContact)
            {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "resolution admits edge {edge:?} without a resolved-open edge cell"
                )));
            }
        }
        for (vertices, cell_id) in &self.face_cells {
            if vertices[0] == vertices[1]
                || vertices[1] == vertices[2]
                || vertices[0] == vertices[2]
            {
                return Err(ConstraintGradingError::DegenerateFace(*vertices));
            }
            let cell = self.complex.cell(*cell_id)?;
            if cell.grade != 2 {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "face {vertices:?} maps to grade {}",
                    cell.grade
                )));
            }
            let face = ConstraintFace {
                id: ConstraintFaceId(cell_id.0),
                source_event: self.source_event,
                vertices: *vertices,
            };
            let mut expected = CausalChain::default();
            for (edge, hand) in face.boundary()? {
                let edge_cell = self.edge_cells.get(&edge).ok_or_else(|| {
                    ConstraintGradingError::FaceBoundaryNotFounded(*vertices)
                })?;
                expected.add_term(
                    *edge_cell,
                    ComparativeMultiplicity::from_hand(hand, 1_u8)?,
                );
            }
            if cell.boundary != expected {
                return Err(ConstraintGradingError::MemberInvariant(format!(
                    "face {vertices:?} boundary disagrees with its edge cells"
                )));
            }
        }
        Ok(())
    }

    /// The cells founded from resolved open contacts, named. Empty for the refusing member.
    ///
    /// [`found_member`] founds `edge_cells` and `edge_provenance` in one pass, so every member
    /// this module returns satisfies `edge_provenance.keys() ⊆ edge_cells.keys()`. This type is
    /// public and `Deserialize`, so a hand-built or remounted value need not: the two maps are
    /// separate fields and nothing in the wire format ties them together. That disagreement is
    /// returned as [`ConstraintGradingError::ProvenanceWithoutCell`] naming the edge, never as an
    /// index panic.
    pub fn resolved_open_cells(
        &self,
    ) -> Result<Vec<(ConstraintEdge, CausalCellId)>, ConstraintGradingError> {
        self.edge_provenance
            .iter()
            .filter(|(_, provenance)| **provenance == EdgeProvenance::ResolvedOpenContact)
            .map(|(edge, _)| {
                self.edge_cells
                    .get(edge)
                    .map(|cell| (*edge, *cell))
                    .ok_or(ConstraintGradingError::ProvenanceWithoutCell(*edge))
            })
            .collect()
    }

    pub fn f_vector(&self) -> BTreeMap<u32, usize> {
        self.complex.f_vector()
    }
}

/// The complete family of graded complexes compatible with one presentation.
///
/// [definition] The family is the adapter's return because the presentation does not determine one
/// complex. Its members are indexed by the resolutions of [`Self::open_contacts`]; the two
/// constructed eagerly are the bounds of that indexing in the inclusion order of 1-cells.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintComplexFamily {
    pub schema: String,
    pub presentation_lineage: String,
    pub source_event: EventId,
    /// The exact open set, each contact with the interval and aperture that could not decide it.
    pub open_contacts: Vec<OpenContact>,
    /// Canonical edges that carry an `Open` reading under one aperture and an `Inside` reading
    /// under another. Their 1-cell exists, so they are not part of the indexing — and they are
    /// retained here rather than dropped.
    pub open_subsumed_by_inside: Vec<ConstraintEdge>,
    /// Every open contact refused. Its incidence is the presented complex's own.
    pub refusing: GradedConstraintComplex,
    /// Every open contact founded.
    pub admitting: GradedConstraintComplex,
}

impl ConstraintComplexFamily {
    /// The presentation decides its own incidence: the family is a singleton.
    pub fn is_determinate(&self) -> bool {
        self.open_contacts.is_empty()
    }

    /// `2^n` for `n` open contacts — exact, and a `BigUint` because it is not bounded by anything.
    pub fn cardinality(&self) -> BigUint {
        BigUint::from(1_u8) << self.open_contacts.len()
    }

    pub fn open_edges(&self) -> Vec<ConstraintEdge> {
        self.open_contacts.iter().map(|open| open.edge).collect()
    }
}

/// The open set of one presentation, and the open readings its own `Inside` readings subsume.
///
/// The first return is ordered by canonical edge and carries one entry per undecided 1-cell. When
/// several apertures leave the same pair open, the first reading in presentation order is the one
/// retained; the pair is one incidence question however many receivers asked it.
pub fn open_contacts(
    complex: &PhysicalConstraintComplex,
) -> Result<(Vec<OpenContact>, Vec<ConstraintEdge>), ConstraintGradingError> {
    let mut inside = BTreeSet::new();
    let mut open = BTreeMap::new();
    for family in &complex.contact_families {
        for reading in &family.readings {
            let (edge, _) = ConstraintEdge::new(reading.left, reading.right)?;
            match reading.class {
                ContactClass::Inside => {
                    inside.insert(edge);
                }
                ContactClass::Open => {
                    open.entry(edge).or_insert_with(|| OpenContact {
                        edge,
                        left: reading.left,
                        right: reading.right,
                        left_component: family.left,
                        right_component: family.right,
                        left_ordinal: reading.left_ordinal,
                        right_ordinal: reading.right_ordinal,
                        aperture_lineage: family.aperture.lineage.clone(),
                        aperture_squared: family.aperture.squared.clone(),
                        squared_distance: reading.squared_distance.clone(),
                    });
                }
                ContactClass::Outside => {}
            }
        }
    }
    let subsumed = open
        .keys()
        .copied()
        .filter(|edge| inside.contains(edge))
        .collect::<Vec<_>>();
    open.retain(|edge, _| !inside.contains(edge));
    Ok((open.into_values().collect(), subsumed))
}

/// One member of the family, under a named law for the open class.
pub fn graded_constraint_member(
    complex: &PhysicalConstraintComplex,
    law: &OpenContactLaw,
) -> Result<GradedConstraintComplex, ConstraintGradingError> {
    let (open, _) = open_contacts(complex)?;
    let resolution = resolve(&open, law)?;
    found_member(complex, resolution)
}

/// The complete family, with its open set and its two bounding members.
pub fn graded_constraint_family(
    complex: &PhysicalConstraintComplex,
) -> Result<ConstraintComplexFamily, ConstraintGradingError> {
    let (open_contacts, open_subsumed_by_inside) = open_contacts(complex)?;
    let refusing = found_member(
        complex,
        resolve(&open_contacts, &OpenContactLaw::RefuseEveryOpen)?,
    )?;
    let admitting = found_member(
        complex,
        resolve(&open_contacts, &OpenContactLaw::AdmitEveryOpen)?,
    )?;
    Ok(ConstraintComplexFamily {
        schema: "holonic-engine.constraint-complex-family.v1".to_owned(),
        presentation_lineage: complex.presentation_lineage.clone(),
        source_event: complex.source_event,
        open_contacts,
        open_subsumed_by_inside,
        refusing,
        admitting,
    })
}

/// Every member of the family, in ascending resolution order, bounded by an explicit ceiling.
///
/// The family has `2^n` members. This refuses above `bound` with the exact count rather than
/// exponentiating quietly.
pub fn enumerate_family(
    complex: &PhysicalConstraintComplex,
    bound: usize,
) -> Result<Vec<GradedConstraintComplex>, ConstraintGradingError> {
    let (open, _) = open_contacts(complex)?;
    let width = open.len();
    if width >= usize::BITS as usize || (1_usize << width) > bound {
        return Err(ConstraintGradingError::OpenFamilyTooWide { open: width, bound });
    }
    let mut members = Vec::with_capacity(1_usize << width);
    for index in 0..(1_usize << width) {
        let resolution = OpenResolution::declared(
            open.iter()
                .enumerate()
                .map(|(at, contact)| (contact.edge, index & (1 << at) != 0)),
        );
        members.push(found_member(complex, resolution)?);
    }
    Ok(members)
}

fn resolve(
    open: &[OpenContact],
    law: &OpenContactLaw,
) -> Result<OpenResolution, ConstraintGradingError> {
    match law {
        OpenContactLaw::RefuseEveryOpen => Ok(OpenResolution::declared(
            open.iter().map(|contact| (contact.edge, false)),
        )),
        OpenContactLaw::AdmitEveryOpen => Ok(OpenResolution::declared(
            open.iter().map(|contact| (contact.edge, true)),
        )),
        OpenContactLaw::Declared(declared) => {
            let expected = open
                .iter()
                .map(|contact| contact.edge)
                .collect::<BTreeSet<_>>();
            for edge in &expected {
                if !declared.admitted.contains_key(edge) {
                    return Err(ConstraintGradingError::UnresolvedOpenContact(*edge));
                }
            }
            for edge in declared.admitted.keys() {
                if !expected.contains(edge) {
                    return Err(ConstraintGradingError::ResolutionNamesNonOpenContact(*edge));
                }
            }
            Ok(declared.clone())
        }
    }
}

fn found_member(
    complex: &PhysicalConstraintComplex,
    resolution: OpenResolution,
) -> Result<GradedConstraintComplex, ConstraintGradingError> {
    let source_events = BTreeSet::from([complex.source_event]);

    // The resolved 1-skeleton and, from it, the 2-cells. The face law is replayed in presentation
    // order exactly as `found_contact_family` enacts it: a family sees its own admitted contacts
    // and every earlier family's, and founds `[pᵢ,pᵢ₊₁,qⱼ]` only where all three 1-faces stand.
    let mut admitted_contacts = BTreeSet::new();
    let mut resolved_open = BTreeSet::new();
    let mut triples = Vec::new();
    let mut seen_triples = BTreeSet::new();
    for family in &complex.contact_families {
        for reading in &family.readings {
            let (edge, _) = ConstraintEdge::new(reading.left, reading.right)?;
            match reading.class {
                ContactClass::Inside => {
                    admitted_contacts.insert(edge);
                }
                ContactClass::Open => {
                    if resolution.is_admitted(&edge) {
                        admitted_contacts.insert(edge);
                        resolved_open.insert(edge);
                    }
                }
                ContactClass::Outside => {}
            }
        }
        let left_vertices = complex.component(family.left)?.vertices.clone();
        let right_vertices = complex.component(family.right)?.vertices.clone();
        for step in left_vertices.windows(2) {
            for right in &right_vertices {
                // A within-component family's junction ranges over the same chain the step comes
                // from, so it meets its own step endpoints. The triple collapses there and founds
                // no triangle, exactly as `found_faces_over` skips it in the constraint owner.
                if *right == step[0] || *right == step[1] {
                    continue;
                }
                let first = ConstraintEdge::new(step[0], *right)?.0;
                let second = ConstraintEdge::new(step[1], *right)?.0;
                if admitted_contacts.contains(&first) && admitted_contacts.contains(&second) {
                    let triple = [step[0], step[1], *right];
                    if triple[0] == triple[1] || triple[1] == triple[2] || triple[0] == triple[2] {
                        return Err(ConstraintGradingError::DegenerateFace(triple));
                    }
                    if seen_triples.insert(triple) {
                        triples.push(triple);
                    }
                }
            }
        }
    }
    // An `Inside` reading under one aperture keeps a 1-cell whose provenance is an admitted
    // contact, whatever another aperture left open about the same pair.
    resolved_open.retain(|edge| !carries_inside(complex, *edge));

    let mut graded = GradedCausalComplex::default();

    let mut vertex_cells = BTreeMap::new();
    for (id, vertex) in &complex.vertices {
        let cell = graded.found_cell(
            format!(
                "vertex(c{}:{}:{})",
                vertex.component.0, vertex.local_ordinal, vertex.monomer
            ),
            source_events.clone(),
            0,
            CausalChain::default(),
        )?;
        vertex_cells.insert(*id, cell);
    }

    let mut edge_cells = BTreeMap::new();
    let mut edge_provenance = BTreeMap::new();
    let mut one_cells = complex.polygonal_edges.clone();
    one_cells.extend(admitted_contacts.iter().copied());
    for edge in &one_cells {
        let provenance = if complex.polygonal_edges.contains(edge) {
            EdgeProvenance::Polygonal
        } else if resolved_open.contains(edge) {
            EdgeProvenance::ResolvedOpenContact
        } else {
            EdgeProvenance::AdmittedContact
        };
        let lower = *vertex_cells
            .get(&edge.lower)
            .ok_or(ConstraintGradingError::EdgeEndpointNotFounded(edge.lower))?;
        let upper = *vertex_cells
            .get(&edge.upper)
            .ok_or(ConstraintGradingError::EdgeEndpointNotFounded(edge.upper))?;
        let mut boundary = CausalChain::default();
        boundary.add_term(upper, ComparativeMultiplicity::positive(1_u8));
        boundary.add_term(lower, ComparativeMultiplicity::negative(1_u8));
        let name = match provenance {
            EdgeProvenance::Polygonal => "polygonal",
            EdgeProvenance::AdmittedContact => "contact",
            EdgeProvenance::ResolvedOpenContact => "resolved-open-contact",
        };
        let cell = graded.found_cell(
            format!("{name}({},{})", edge.lower.0, edge.upper.0),
            source_events.clone(),
            1,
            boundary,
        )?;
        edge_cells.insert(*edge, cell);
        edge_provenance.insert(*edge, provenance);
    }

    let mut face_cells = BTreeMap::new();
    for (at, triple) in triples.iter().enumerate() {
        // The alternating hand is the constraint owner's, replayed rather than restated here.
        let face = ConstraintFace {
            id: ConstraintFaceId(at as u64 + 1),
            source_event: complex.source_event,
            vertices: *triple,
        };
        let mut boundary = CausalChain::default();
        for (edge, hand) in face.boundary()? {
            let cell = *edge_cells
                .get(&edge)
                .ok_or(ConstraintGradingError::FaceBoundaryNotFounded(*triple))?;
            boundary.add_term(cell, ComparativeMultiplicity::from_hand(hand, 1_u8)?);
        }
        let cell = graded.found_cell(
            format!("face({},{},{})", triple[0].0, triple[1].0, triple[2].0),
            source_events.clone(),
            2,
            boundary,
        )?;
        face_cells.insert(*triple, cell);
    }

    graded.validate()?;
    Ok(GradedConstraintComplex {
        schema: "holonic-engine.graded-constraint-complex.v1".to_owned(),
        presentation_lineage: complex.presentation_lineage.clone(),
        source_event: complex.source_event,
        resolution,
        complex: graded,
        vertex_cells,
        edge_cells,
        edge_provenance,
        face_cells,
    })
}

fn carries_inside(complex: &PhysicalConstraintComplex, edge: ConstraintEdge) -> bool {
    complex.contact_families.iter().any(|family| {
        family.readings.iter().any(|reading| {
            reading.class == ContactClass::Inside
                && ConstraintEdge::new(reading.left, reading.right)
                    .map(|(candidate, _)| candidate == edge)
                    .unwrap_or(false)
        })
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ConstraintGradingError {
    #[error("the presented constraint complex refused: {0}")]
    Constraint(#[from] ConstraintError),
    #[error("the graded complex refused: {0}")]
    Algebraic(#[from] CausalAlgebraicError),
    #[error("open contact {0:?} carries no declared resolution")]
    UnresolvedOpenContact(ConstraintEdge),
    #[error(
        "the declared resolution names {0:?}, which is not an open contact of this presentation"
    )]
    ResolutionNamesNonOpenContact(ConstraintEdge),
    #[error(
        "the two-cell on {0:?} is degenerate; a triple repeating an occurrence founds no triangle"
    )]
    DegenerateFace([ConstraintVertexId; 3]),
    #[error("the two-cell on {0:?} has a boundary edge that was never founded")]
    FaceBoundaryNotFounded([ConstraintVertexId; 3]),
    #[error("the one-cell endpoint {0:?} is absent from this presentation")]
    EdgeEndpointNotFounded(ConstraintVertexId),
    #[error(
        "the one-cell {0:?} carries a declared provenance but no founded cell; this member's edge_provenance and edge_cells disagree"
    )]
    ProvenanceWithoutCell(ConstraintEdge),
    #[error("the remounted graded member violates an internal invariant: {0}")]
    MemberInvariant(String),
    #[error(
        "this presentation carries {open} open contacts, so its family has 2^{open} members; enumeration was bounded at {bound}"
    )]
    OpenFamilyTooWide { open: usize, bound: usize },
}

#[cfg(test)]
#[path = "physical_constraint_grading/tests.rs"]
mod tests;
