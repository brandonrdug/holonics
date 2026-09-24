//! Exact local constraint incidence for one addressed physical presentation.
//!
//! This owner does not know proteins, atom names, predictors, or assays. A surface codec presents
//! lineaged polygonal components as coordinate boxes and a resident carrier presents the contact
//! class of every declared component pair. This module verifies that testimony exactly, founds the
//! corresponding one- and two-cells, and returns the boundary and unresolved fibre.
//!
//! A contact is not inferred from a rounded distance. For an exact squared-distance interval `D`
//! and aperture `a`, `D.upper <= a` is inside, `D.lower > a` is outside, and every overlap remains
//! open. The two-cell `[pᵢ,pᵢ₊₁,qⱼ]` exists only when the polygonal edge `pᵢ→pᵢ₊₁` and both contact
//! edges are present. Its algebraic boundary is derived with the usual alternating hand.
//!
//! # Two contact laws, one contact class
//!
//! [definition] A contact family is founded under one of two **population** laws, named by
//! [`ContactFamilyKind`]. The `Inside`/`Outside`/`Open` law that classifies each pair is the same
//! one in both.
//!
//! - [`ContactFamilyKind::Cross`] — [`PhysicalConstraintComplex::found_contact_family`] takes two
//!   components and reads every cross pair. It cannot express a pair of one component: at the
//!   diagonal the edge collapses ([`ConstraintError::CollapsedEdge`]).
//! - [`ContactFamilyKind::WithinComponent`] —
//!   [`PhysicalConstraintComplex::found_within_component_contact_family`] takes one component and
//!   reads the unordered pairs `i < j` of its own chain whose positions differ by at least a
//!   **declared** sequence separation `k`. There is no default `k`; the caller states it.
//!
//! [definition] The separation exclusion is what makes the within-component family a contact
//! reading at all. `|i − j| = 1` is the presented chain's own step — a *covalent* 1-cell, founded
//! by [`PhysicalConstraintComplex::found`] as a [`ConstraintEdge`] of `polygonal_edges` whatever
//! any aperture says, and carrying no information about how the chain folds. So `k = 1` names
//! nothing an unordered pair does not already exclude and `k` below `2` is refused by name. The
//! protein reading of this family is the intra-chain contact; `k = 3` and `k = 4` are the usual
//! declarations there, and this owner takes neither as a default.
//!
//! The within-component population is exact: for a component of extent `n` and separation `k ≥ 2`,
//! `C(n − k + 1, 2)` pairs, returned by [`within_component_pair_count`] and proved in
//! `Foundation/AperturedGradedComplex.lean` (`withinComponentPairs_card`). `k ≥ 2` is the declared
//! domain of that count as well as of the founders: below it the Lean family is not a family of
//! unordered pairs at all (`withinComponentPairs_zero_contains_the_diagonal`).
//!
//! # Several families are a family of complexes
//!
//! [definition] A complex may carry several founded families — a second aperture, a second
//! declared separation, a second component pair — and they are **not** one complex over the union
//! of their contacts. The 2-cell law of [`PhysicalConstraintComplex::found_contact_family`] and
//! [`PhysicalConstraintComplex::found_within_component_contact_family`] is therefore asked of each
//! founding against *that founding's own* admitted contacts, and each founding's 2-cell population
//! is recorded beside it in [`PhysicalConstraintComplex::family_faces`], readable through
//! [`PhysicalConstraintComplex::family_faces`] and
//! [`PhysicalConstraintComplex::two_chain_boundary_of_family`].
//!
//! [definition] The 2-cell population itself is a **set of vertex triples**: a triple two
//! foundings both reach carries one cell, minted once, whose boundary is added to
//! [`ComplexBoundary::two_chain_boundary`] once. [`PhysicalConstraintComplex::contact_edges`] remains the complex-wide
//! 1-skeleton — it is what [`crate::physical_constraint_grading`] grades a member over, and that
//! module replays the face law in presentation order with its own duplicate-triple guard.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::EventId;
use holonics::exact_value::ExactInterval;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConstraintVertexId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConstraintComponentId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConstraintFaceId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinateBox3 {
    pub x: ExactInterval,
    pub y: ExactInterval,
    pub z: ExactInterval,
}

impl CoordinateBox3 {
    pub fn point(x: Rat, y: Rat, z: Rat) -> Self {
        Self {
            x: ExactInterval::point(x),
            y: ExactInterval::point(y),
            z: ExactInterval::point(z),
        }
    }

    pub fn squared_distance(&self, other: &Self) -> ExactInterval {
        let dx = difference(&self.x, &other.x);
        let dy = difference(&self.y, &other.y);
        let dz = difference(&self.z, &other.z);
        let dx = square(&dx);
        let dy = square(&dy);
        let dz = square(&dz);
        ExactInterval {
            lower: dx.lower + dy.lower + dz.lower,
            upper: dx.upper + dy.upper + dz.upper,
        }
    }
}

fn difference(left: &ExactInterval, right: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &left.lower - &right.upper,
        upper: &left.upper - &right.lower,
    }
}

fn square(value: &ExactInterval) -> ExactInterval {
    let lower_square = &value.lower * &value.lower;
    let upper_square = &value.upper * &value.upper;
    let lower = if value.lower <= Rat::zero() && Rat::zero() <= value.upper {
        Rat::zero()
    } else {
        lower_square.clone().min(upper_square.clone())
    };
    ExactInterval {
        lower,
        upper: lower_square.max(upper_square),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidueMaterial {
    pub source_ordinal: i32,
    pub monomer: String,
    pub position: CoordinateBox3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComponentMaterial {
    /// Exterior source lineage, retained as testimony and never used as a semantic taxon.
    pub lineage: String,
    pub residues: Vec<ResidueMaterial>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintVertex {
    pub id: ConstraintVertexId,
    pub component: ConstraintComponentId,
    pub local_ordinal: u32,
    pub source_ordinal: i32,
    pub monomer: String,
    pub position: CoordinateBox3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentedComponent {
    pub id: ConstraintComponentId,
    pub lineage: String,
    pub vertices: Vec<ConstraintVertexId>,
    pub sequence: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConstraintEdge {
    pub lower: ConstraintVertexId,
    pub upper: ConstraintVertexId,
}

impl ConstraintEdge {
    pub fn new(
        left: ConstraintVertexId,
        right: ConstraintVertexId,
    ) -> Result<(Self, i8), ConstraintError> {
        if left == right {
            return Err(ConstraintError::CollapsedEdge(left));
        }
        Ok(if left < right {
            (
                Self {
                    lower: left,
                    upper: right,
                },
                1,
            )
        } else {
            (
                Self {
                    lower: right,
                    upper: left,
                },
                -1,
            )
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContactClass {
    Outside,
    Inside,
    Open,
}

impl ContactClass {
    pub const fn wire(self) -> u8 {
        match self {
            Self::Outside => 0,
            Self::Inside => 1,
            Self::Open => 2,
        }
    }

    pub fn from_wire(value: u8) -> Result<Self, ConstraintError> {
        match value {
            0 => Ok(Self::Outside),
            1 => Ok(Self::Inside),
            2 => Ok(Self::Open),
            _ => Err(ConstraintError::UnknownContactClass(value)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DistanceAperture {
    pub lineage: String,
    pub squared: Rat,
}

impl DistanceAperture {
    pub fn classify(&self, distance_squared: &ExactInterval) -> ContactClass {
        if distance_squared.upper <= self.squared {
            ContactClass::Inside
        } else if distance_squared.lower > self.squared {
            ContactClass::Outside
        } else {
            ContactClass::Open
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PairUncertainty {
    pub source_lineage: String,
    pub row_given_column_bits: u16,
    pub column_given_row_bits: u16,
    pub row_given_column: ExactInterval,
    pub column_given_row: ExactInterval,
    pub row_given_column_ulp: Rat,
    pub column_given_row_ulp: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactReading {
    pub left: ConstraintVertexId,
    pub right: ConstraintVertexId,
    pub left_ordinal: u32,
    pub right_ordinal: u32,
    pub squared_distance: ExactInterval,
    pub class: ContactClass,
    pub uncertainty: Option<PairUncertainty>,
}

/// Which population law founded a contact family.
///
/// [definition] This names the **pairs the family reads**, never the class it reads them into: the
/// exact `Inside`/`Outside`/`Open` trichotomy of [`DistanceAperture::classify`] is the same law in
/// both kinds.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub enum ContactFamilyKind {
    /// Every pair of one ordered pair of **distinct** components, row-major in the left
    /// component's chain order. The only kind founded before this law was written, so a wire that
    /// carries no word decodes as this one.
    #[default]
    Cross,
    /// The unordered pairs `i < j` of **one** component whose chain positions differ by at least
    /// `minimum_separation`, in ascending `i` then ascending `j`.
    WithinComponent {
        /// The declared sequence-separation exclusion `k`. Always at least `2`: `k = 1` would
        /// name the presented chain's own covalent step, which is a `polygonal_edges` 1-cell and
        /// not a contact.
        minimum_separation: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ContactFamilyWire")]
pub struct ContactFamily {
    pub left: ConstraintComponentId,
    pub right: ConstraintComponentId,
    /// Which population law founded this family. `left == right` exactly when it is
    /// [`ContactFamilyKind::WithinComponent`].
    #[serde(default)]
    pub kind: ContactFamilyKind,
    pub aperture: DistanceAperture,
    /// The complete receiver population, including outside and open pairs.
    pub readings: Vec<ContactReading>,
}

/// The wire of a [`ContactFamily`]. A remounted family passes the same kind coherence its founders
/// enforce: a within-component family names one component with a separation of at least two, and
/// a cross family names two distinct components.
#[derive(Deserialize)]
struct ContactFamilyWire {
    left: ConstraintComponentId,
    right: ConstraintComponentId,
    #[serde(default)]
    kind: ContactFamilyKind,
    aperture: DistanceAperture,
    readings: Vec<ContactReading>,
}

impl TryFrom<ContactFamilyWire> for ContactFamily {
    type Error = ConstraintError;

    fn try_from(wire: ContactFamilyWire) -> Result<Self, Self::Error> {
        match wire.kind {
            ContactFamilyKind::WithinComponent { minimum_separation } => {
                if minimum_separation < 2 {
                    return Err(ConstraintError::SeparationIsCovalent(minimum_separation));
                }
                if wire.left != wire.right {
                    return Err(ConstraintError::FamilyKindDisagreesWithItsComponents);
                }
            }
            ContactFamilyKind::Cross => {
                if wire.left == wire.right {
                    return Err(ConstraintError::FamilyKindDisagreesWithItsComponents);
                }
            }
        }
        Ok(Self {
            left: wire.left,
            right: wire.right,
            kind: wire.kind,
            aperture: wire.aperture,
            readings: wire.readings,
        })
    }
}

impl ContactFamily {
    /// The declared sequence separation, when this family is a within-component one.
    pub const fn minimum_separation(&self) -> Option<u32> {
        match self.kind {
            ContactFamilyKind::Cross => None,
            ContactFamilyKind::WithinComponent { minimum_separation } => Some(minimum_separation),
        }
    }
}

/// `C(n − k + 1, 2)`: the exact population of the within-component family of a component of extent
/// `n` under a declared sequence separation `k`.
///
/// # Domain
///
/// [definition] `k ≥ 2`, which is the domain every founder in this module declares
/// ([`ConstraintError::SeparationIsCovalent`]), and this function refuses below it rather than
/// returning a number for a family nobody may found. The refusal is not decoration: the Lean
/// family `Foundation/AperturedGradedComplex.lean::withinComponentPairs` is `{(i, j) : i + k ≤ j}`,
/// so at `k = 0` it contains the whole diagonal (`withinComponentPairs_zero_contains_the_diagonal`)
/// and its cardinality is `C(n + 1, 2)` and **not** the `C(n, 2)` an unordered-pair reading of the
/// docstring would suggest. `withinComponentPairs_lt` — the theorem that every member really is an
/// unordered pair `i < j` — carries the hypothesis `1 ≤ k` for exactly that reason, and this
/// owner's own contact reading needs `2 ≤ k`. Rather than carry two readings of one name, the
/// domain is `k ≥ 2` here and the `k < 2` answer is `None`.
///
/// On that domain the pairs are `i < j` in `1..=n` with `j − i ≥ k`, so the count is
/// `∑_{d=k}^{n−1} (n − d) = (n − k)(n − k + 1)/2 = C(n − k + 1, 2)`, which is `0` as soon as
/// `n ≤ k`.
///
/// # Returns
///
/// `None` when `k < 2` (outside the domain) or when the product overflows the machine integer —
/// the count is quadratic in the presented extent, so the bound is taken rather than assumed.
///
/// Lean owner: `Foundation/AperturedGradedComplex.lean`, `withinComponentPairs_card` (stated for
/// `1 ≤ k`) and `withinComponentPairs_zero_contains_the_diagonal` (why `k = 0` is excluded).
pub fn within_component_pair_count(extent: usize, minimum_separation: u32) -> Option<usize> {
    if minimum_separation < 2 {
        return None;
    }
    let span = extent.saturating_sub(minimum_separation as usize);
    span.checked_mul(span.checked_add(1)?).map(|product| product / 2)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintFace {
    pub id: ConstraintFaceId,
    pub source_event: EventId,
    pub vertices: [ConstraintVertexId; 3],
}

impl ConstraintFace {
    pub fn boundary(&self) -> Result<[(ConstraintEdge, i8); 3], ConstraintError> {
        // ∂[a,b,c] = [b,c] - [a,c] + [a,b]. `ConstraintEdge::new` supplies the hand relative to
        // the canonical edge orientation; the middle face carries the additional minus sign.
        let [a, b, c] = self.vertices;
        let (bc, h_bc) = ConstraintEdge::new(b, c)?;
        let (ac, h_ac) = ConstraintEdge::new(a, c)?;
        let (ab, h_ab) = ConstraintEdge::new(a, b)?;
        Ok([(bc, h_bc), (ac, -h_ac), (ab, h_ab)])
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComponentBoundary {
    pub component: ConstraintComponentId,
    pub head: ConstraintVertexId,
    pub tail: ConstraintVertexId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComplexBoundary {
    pub polygonal_ends: Vec<ComponentBoundary>,
    /// Nonzero coefficients of the algebraic boundary of the complete two-cell population.
    pub two_chain_boundary: BTreeMap<ConstraintEdge, i64>,
}

/// The schema every complex this module founds declares.
pub const PHYSICAL_CONSTRAINT_COMPLEX_SCHEMA: &str = "holonic-engine.physical-constraint-complex.v1";

/// **One addressed physical presentation, its founded families, and their cells.**
///
/// # What a remounted complex is testimony for
///
/// [implemented-exact] The wire route is gated: `Deserialize` goes through
/// [`PhysicalConstraintComplexWire`] and [`TryFrom`], which re-checks the complex's *structural*
/// coherence before it is carried — the schema, that every addressed id is in range, that every
/// face's three vertices are presented and its two contact edges stand, that
/// [`ComplexBoundary::two_chain_boundary`] is exactly the boundary recomputed from
/// [`Self::faces`], that `∂∘∂ = 0`, that no vertex triple carries two faces, and that
/// [`Self::family_faces`] is aligned with [`Self::contact_families`] and names only standing
/// faces.
///
/// [definition] What it does **not** re-check is the *material* law: a remounted complex is not
/// testimony that each reading's class is the class
/// [`DistanceAperture::classify`] returns on the presented coordinates, because the wire may
/// carry coordinates that were never the ones the classes were read from. Only
/// [`Self::found_contact_family`] and [`Self::found_within_component_contact_family`] audit the
/// enacted class against the exact interval law. A remounted complex is therefore testimony that
/// *a coherent complex of this shape was serialized*, and the material audit must be re-enacted
/// from the presentation to be claimed again.
#[derive(Debug, Serialize, Deserialize)]
#[serde(try_from = "PhysicalConstraintComplexWire")]
pub struct PhysicalConstraintComplex {
    pub schema: String,
    pub presentation_lineage: String,
    pub source_event: EventId,
    pub components: BTreeMap<ConstraintComponentId, PresentedComponent>,
    pub vertices: BTreeMap<ConstraintVertexId, ConstraintVertex>,
    pub polygonal_edges: BTreeSet<ConstraintEdge>,
    pub contact_families: Vec<ContactFamily>,
    pub contact_edges: BTreeSet<ConstraintEdge>,
    pub faces: BTreeMap<ConstraintFaceId, ConstraintFace>,
    /// The 2-cells each founded family stands over, aligned index for index with
    /// [`Self::contact_families`]. A cell reached by two families appears in both entries; it is
    /// minted once and its boundary is added once.
    pub family_faces: Vec<Vec<ConstraintFaceId>>,
    pub boundary: ComplexBoundary,
    next_face: u64,
}

/// The wire of a [`PhysicalConstraintComplex`]. Every field is re-checked by the `TryFrom` below.
#[derive(Deserialize)]
pub struct PhysicalConstraintComplexWire {
    schema: String,
    presentation_lineage: String,
    source_event: EventId,
    components: BTreeMap<ConstraintComponentId, PresentedComponent>,
    vertices: BTreeMap<ConstraintVertexId, ConstraintVertex>,
    polygonal_edges: BTreeSet<ConstraintEdge>,
    contact_families: Vec<ContactFamily>,
    contact_edges: BTreeSet<ConstraintEdge>,
    faces: BTreeMap<ConstraintFaceId, ConstraintFace>,
    family_faces: Vec<Vec<ConstraintFaceId>>,
    boundary: ComplexBoundary,
    next_face: u64,
}

impl TryFrom<PhysicalConstraintComplexWire> for PhysicalConstraintComplex {
    type Error = ConstraintError;

    fn try_from(wire: PhysicalConstraintComplexWire) -> Result<Self, Self::Error> {
        if wire.schema != PHYSICAL_CONSTRAINT_COMPLEX_SCHEMA {
            return Err(ConstraintError::RemountedSchemaMismatch(wire.schema));
        }
        // Every addressed occurrence is presented, and every presented occurrence belongs to a
        // presented component.
        for (id, vertex) in &wire.vertices {
            if vertex.id != *id {
                return Err(ConstraintError::RemountedVertexMisaddressed(*id));
            }
            if !wire.components.contains_key(&vertex.component) {
                return Err(ConstraintError::MissingComponent(vertex.component));
            }
        }
        for (id, component) in &wire.components {
            if component.id != *id {
                return Err(ConstraintError::MissingComponent(*id));
            }
            for vertex in &component.vertices {
                if !wire.vertices.contains_key(vertex) {
                    return Err(ConstraintError::RemountedVertexAbsent(*vertex));
                }
            }
        }
        for edge in wire.polygonal_edges.iter().chain(wire.contact_edges.iter()) {
            for endpoint in [edge.lower, edge.upper] {
                if !wire.vertices.contains_key(&endpoint) {
                    return Err(ConstraintError::RemountedVertexAbsent(endpoint));
                }
            }
        }
        for family in &wire.contact_families {
            for component in [family.left, family.right] {
                if !wire.components.contains_key(&component) {
                    return Err(ConstraintError::MissingComponent(component));
                }
            }
            for reading in &family.readings {
                for endpoint in [reading.left, reading.right] {
                    if !wire.vertices.contains_key(&endpoint) {
                        return Err(ConstraintError::RemountedVertexAbsent(endpoint));
                    }
                }
            }
        }
        // Every 2-cell is addressed once, stands on presented occurrences, and its two contact
        // edges stand. The boundary is recomputed rather than trusted.
        let mut triples: BTreeSet<[ConstraintVertexId; 3]> = BTreeSet::new();
        let mut recomputed: BTreeMap<ConstraintEdge, i64> = BTreeMap::new();
        let one_cells: BTreeSet<ConstraintEdge> = wire
            .polygonal_edges
            .iter()
            .chain(wire.contact_edges.iter())
            .copied()
            .collect();
        for (id, face) in &wire.faces {
            if face.id != *id {
                return Err(ConstraintError::RemountedFaceMisaddressed(*id));
            }
            if id.0 >= wire.next_face {
                return Err(ConstraintError::RemountedFaceMisaddressed(*id));
            }
            for vertex in face.vertices {
                if !wire.vertices.contains_key(&vertex) {
                    return Err(ConstraintError::RemountedVertexAbsent(vertex));
                }
            }
            if !triples.insert(face.vertices) {
                return Err(ConstraintError::RemountedDuplicateFace(face.vertices));
            }
            for (edge, hand) in face.boundary()? {
                if !one_cells.contains(&edge) {
                    return Err(ConstraintError::RemountedFaceEdgeAbsent(face.vertices));
                }
                *recomputed.entry(edge).or_default() += i64::from(hand);
            }
        }
        recomputed.retain(|_, hand| *hand != 0);
        if recomputed != wire.boundary.two_chain_boundary {
            return Err(ConstraintError::RemountedBoundaryDisagrees);
        }
        // ∂∘∂ = 0 on the carried 2-chain.
        let mut endpoints: BTreeMap<ConstraintVertexId, i64> = BTreeMap::new();
        for (edge, hand) in &recomputed {
            *endpoints.entry(edge.lower).or_default() -= *hand;
            *endpoints.entry(edge.upper).or_default() += *hand;
        }
        endpoints.retain(|_, coefficient| *coefficient != 0);
        if !endpoints.is_empty() {
            return Err(ConstraintError::RemountedBoundaryOfBoundaryNonzero);
        }
        // The per-family face populations are aligned and name standing cells.
        if wire.family_faces.len() != wire.contact_families.len() {
            return Err(ConstraintError::RemountedFamilyFacesMisaligned {
                families: wire.contact_families.len(),
                populations: wire.family_faces.len(),
            });
        }
        for population in &wire.family_faces {
            for face in population {
                if !wire.faces.contains_key(face) {
                    return Err(ConstraintError::RemountedFaceMisaddressed(*face));
                }
            }
        }
        Ok(Self {
            schema: wire.schema,
            presentation_lineage: wire.presentation_lineage,
            source_event: wire.source_event,
            components: wire.components,
            vertices: wire.vertices,
            polygonal_edges: wire.polygonal_edges,
            contact_families: wire.contact_families,
            contact_edges: wire.contact_edges,
            faces: wire.faces,
            family_faces: wire.family_faces,
            boundary: wire.boundary,
            next_face: wire.next_face,
        })
    }
}

impl PhysicalConstraintComplex {
    pub fn found(
        presentation_lineage: impl Into<String>,
        source_event: EventId,
        material: Vec<ComponentMaterial>,
    ) -> Result<Self, ConstraintError> {
        let mut components = BTreeMap::new();
        let mut vertices = BTreeMap::new();
        let mut polygonal_edges = BTreeSet::new();
        let mut polygonal_ends = Vec::new();
        let mut next_vertex = 1_u64;
        for (component_at, component) in material.into_iter().enumerate() {
            if component.residues.is_empty() {
                return Err(ConstraintError::EmptyComponent(component.lineage));
            }
            let id = ConstraintComponentId(component_at as u64 + 1);
            let mut ids = Vec::with_capacity(component.residues.len());
            let mut sequence = Vec::with_capacity(component.residues.len());
            for (local_ordinal, residue) in component.residues.into_iter().enumerate() {
                let vertex = ConstraintVertexId(next_vertex);
                next_vertex += 1;
                sequence.push(residue.monomer.clone());
                ids.push(vertex);
                vertices.insert(
                    vertex,
                    ConstraintVertex {
                        id: vertex,
                        component: id,
                        local_ordinal: local_ordinal as u32 + 1,
                        source_ordinal: residue.source_ordinal,
                        monomer: residue.monomer,
                        position: residue.position,
                    },
                );
            }
            for pair in ids.windows(2) {
                polygonal_edges.insert(ConstraintEdge::new(pair[0], pair[1])?.0);
            }
            polygonal_ends.push(ComponentBoundary {
                component: id,
                head: ids[0],
                tail: *ids.last().expect("a nonempty component has a tail"),
            });
            components.insert(
                id,
                PresentedComponent {
                    id,
                    lineage: component.lineage,
                    vertices: ids,
                    sequence,
                },
            );
        }
        Ok(Self {
            schema: PHYSICAL_CONSTRAINT_COMPLEX_SCHEMA.to_owned(),
            presentation_lineage: presentation_lineage.into(),
            source_event,
            components,
            vertices,
            polygonal_edges,
            contact_families: Vec::new(),
            contact_edges: BTreeSet::new(),
            faces: BTreeMap::new(),
            family_faces: Vec::new(),
            boundary: ComplexBoundary {
                polygonal_ends,
                two_chain_boundary: BTreeMap::new(),
            },
            next_face: 1,
        })
    }

    /// Found one complete cross-component receiver family from resident classifications. The CPU
    /// recomputation here is an admission audit: the returned class remains the enacted class, and
    /// any disagreement refuses before incidence is changed.
    pub fn found_contact_family(
        &mut self,
        left: ConstraintComponentId,
        right: ConstraintComponentId,
        aperture: DistanceAperture,
        enacted: &[ContactClass],
        uncertainty: &BTreeMap<(u32, u32), PairUncertainty>,
    ) -> Result<(), ConstraintError> {
        let left_vertices = self.component(left)?.vertices.clone();
        let right_vertices = self.component(right)?.vertices.clone();
        let expected = left_vertices.len() * right_vertices.len();
        if enacted.len() != expected {
            return Err(ConstraintError::ContactPopulationDisagrees {
                expected,
                enacted: enacted.len(),
            });
        }
        if uncertainty.len() != expected {
            return Err(ConstraintError::UncertaintyPopulationDisagrees {
                expected,
                supplied: uncertainty.len(),
            });
        }
        let mut readings = Vec::with_capacity(expected);
        // This family's own admitted contacts. The 2-cell law below is asked of them alone.
        let mut admitted: BTreeSet<ConstraintEdge> = BTreeSet::new();
        for (left_at, left_vertex) in left_vertices.iter().enumerate() {
            for (right_at, right_vertex) in right_vertices.iter().enumerate() {
                let at = left_at * right_vertices.len() + right_at;
                let distance = self.vertices[left_vertex]
                    .position
                    .squared_distance(&self.vertices[right_vertex].position);
                let exact = aperture.classify(&distance);
                if enacted[at] != exact {
                    return Err(ConstraintError::CarrierDisagrees {
                        left_ordinal: left_at as u32 + 1,
                        right_ordinal: right_at as u32 + 1,
                        enacted: enacted[at],
                        exact,
                    });
                }
                let pair = (left_at as u32 + 1, right_at as u32 + 1);
                let reading = ContactReading {
                    left: *left_vertex,
                    right: *right_vertex,
                    left_ordinal: pair.0,
                    right_ordinal: pair.1,
                    squared_distance: distance,
                    class: enacted[at],
                    uncertainty: uncertainty.get(&pair).cloned(),
                };
                if reading.uncertainty.is_none() {
                    return Err(ConstraintError::MissingUncertainty(pair));
                }
                if reading.class == ContactClass::Inside {
                    let edge = ConstraintEdge::new(reading.left, reading.right)?.0;
                    admitted.insert(edge);
                    self.contact_edges.insert(edge);
                }
                readings.push(reading);
            }
        }

        let owned = self.found_faces_over(&left_vertices, &right_vertices, &admitted)?;
        self.contact_families.push(ContactFamily {
            left,
            right,
            kind: ContactFamilyKind::Cross,
            aperture,
            readings,
        });
        self.family_faces.push(owned);
        Ok(())
    }

    /// Found the complete **within-component** receiver family of one presented component, under a
    /// declared sequence-separation exclusion.
    ///
    /// [definition] The population is the unordered pairs `i < j` of the component's own chain
    /// with `j − i ≥ minimum_separation`, addressed by their one-based local ordinals and read in
    /// ascending `i` then ascending `j`. `enacted` carries one class per pair in that order and
    /// `uncertainty` one reading per addressed pair, exactly as
    /// [`Self::found_contact_family`] takes them for a cross family. The contact law itself —
    /// [`DistanceAperture::classify`]'s `Inside`/`Outside`/`Open` trichotomy — is unchanged, and
    /// an `Open` pair is carried into [`Self::contact_families`] as a family member exactly as a
    /// cross `Open` pair is, to be resolved by
    /// [`crate::physical_constraint_grading`] and never here.
    ///
    /// `minimum_separation` is **declared and has no default**. Below `2` it is refused by name:
    /// a pair at separation `1` is the presented chain's own covalent step, already founded as a
    /// `polygonal_edges` 1-cell whatever the aperture says.
    ///
    /// The 2-cell law is the one [`Self::found_contact_family`] enacts, with the junction ranging
    /// over the same component: `[pᵢ, pᵢ₊₁, q]` stands when the chain step and both contact edges
    /// stand and `q` is neither `pᵢ` nor `pᵢ₊₁`. A junction that coincides with a step endpoint
    /// founds no triangle and is skipped rather than refused, which is the only place this law
    /// differs from the cross one.
    pub fn found_within_component_contact_family(
        &mut self,
        component: ConstraintComponentId,
        minimum_separation: u32,
        aperture: DistanceAperture,
        enacted: &[ContactClass],
        uncertainty: &BTreeMap<(u32, u32), PairUncertainty>,
    ) -> Result<(), ConstraintError> {
        if minimum_separation < 2 {
            return Err(ConstraintError::SeparationIsCovalent(minimum_separation));
        }
        let vertices = self.component(component)?.vertices.clone();
        let expected = within_component_pair_count(vertices.len(), minimum_separation).ok_or(
            ConstraintError::WithinComponentPopulationOverflows {
                extent: vertices.len(),
            },
        )?;
        if enacted.len() != expected {
            return Err(ConstraintError::ContactPopulationDisagrees {
                expected,
                enacted: enacted.len(),
            });
        }
        if uncertainty.len() != expected {
            return Err(ConstraintError::UncertaintyPopulationDisagrees {
                expected,
                supplied: uncertainty.len(),
            });
        }
        // `expected` is a function of the presented extent, which is material, and of a declared
        // separation that only shrinks it; both supplied populations are checked against it above
        // before anything is allocated to it.
        let mut readings = Vec::with_capacity(expected);
        // This family's own admitted contacts. The 2-cell law below is asked of them alone.
        let mut admitted: BTreeSet<ConstraintEdge> = BTreeSet::new();
        let separation = minimum_separation as usize;
        let mut at = 0_usize;
        for left_at in 0..vertices.len() {
            for right_at in left_at.saturating_add(separation).min(vertices.len())..vertices.len() {
                let left_vertex = vertices[left_at];
                let right_vertex = vertices[right_at];
                let distance = self.vertices[&left_vertex]
                    .position
                    .squared_distance(&self.vertices[&right_vertex].position);
                let exact = aperture.classify(&distance);
                let pair = (left_at as u32 + 1, right_at as u32 + 1);
                // The enumeration realizes `C(n − k + 1, 2)`, which is what `expected` counted and
                // what `enacted.len()` was checked against; the reading is still taken by `get`
                // rather than by index, so a divergence is the population refusal and not a panic.
                let &carried =
                    enacted
                        .get(at)
                        .ok_or(ConstraintError::ContactPopulationDisagrees {
                            expected,
                            enacted: enacted.len(),
                        })?;
                if carried != exact {
                    return Err(ConstraintError::CarrierDisagrees {
                        left_ordinal: pair.0,
                        right_ordinal: pair.1,
                        enacted: carried,
                        exact,
                    });
                }
                let reading = ContactReading {
                    left: left_vertex,
                    right: right_vertex,
                    left_ordinal: pair.0,
                    right_ordinal: pair.1,
                    squared_distance: distance,
                    class: carried,
                    uncertainty: uncertainty.get(&pair).cloned(),
                };
                if reading.uncertainty.is_none() {
                    return Err(ConstraintError::MissingUncertainty(pair));
                }
                if reading.class == ContactClass::Inside {
                    let edge = ConstraintEdge::new(reading.left, reading.right)?.0;
                    admitted.insert(edge);
                    self.contact_edges.insert(edge);
                }
                readings.push(reading);
                at += 1;
            }
        }
        debug_assert_eq!(at, expected, "the enumeration realizes C(n − k + 1, 2)");
        let owned = self.found_faces_over(&vertices, &vertices, &admitted)?;
        self.contact_families.push(ContactFamily {
            left: component,
            right: component,
            kind: ContactFamilyKind::WithinComponent { minimum_separation },
            aperture,
            readings,
        });
        self.family_faces.push(owned);
        Ok(())
    }

    /// The addressed ordinal pairs of one component's within-component family, in the canonical
    /// order [`Self::found_within_component_contact_family`] reads them.
    ///
    /// A carrier enacting the family uses this to address its own classification; the founding
    /// then audits that classification against the exact interval law pair by pair.
    pub fn within_component_pairs(
        &self,
        component: ConstraintComponentId,
        minimum_separation: u32,
    ) -> Result<Vec<(u32, u32)>, ConstraintError> {
        if minimum_separation < 2 {
            return Err(ConstraintError::SeparationIsCovalent(minimum_separation));
        }
        let extent = self.component(component)?.vertices.len();
        let expected = within_component_pair_count(extent, minimum_separation)
            .ok_or(ConstraintError::WithinComponentPopulationOverflows { extent })?;
        let separation = minimum_separation as usize;
        let mut pairs = Vec::with_capacity(expected);
        for left_at in 0..extent {
            for right_at in left_at.saturating_add(separation).min(extent)..extent {
                pairs.push((left_at as u32 + 1, right_at as u32 + 1));
            }
        }
        Ok(pairs)
    }

    /// The 2-cell law of **one founded family**: one chain step and two contacts admitted *by that
    /// family* to the same junction. No display triangulation is promoted into topology.
    ///
    /// A junction coinciding with a step endpoint founds no triangle — the triple would collapse —
    /// and is skipped. For a cross family that never happens, so this is the cross law unchanged;
    /// for a within-component family it is the only adjustment the diagonal needs.
    ///
    /// # The law is per family, and the 2-cell population is a set
    ///
    /// [definition] `admitted` is the founding family's **own** `Inside` edge set, not the
    /// complex-wide union [`Self::contact_edges`]. A complex carrying several families at
    /// different apertures or different declared separations is a *family of complexes*; asking
    /// the 2-cell law of one family against the union of every family's edges would found cells
    /// no single aperture admits. For any two families addressed to different `(left, right)`
    /// component pairs the two readings coincide — a cross family `(L, R)` queries only `L × R`
    /// edges and a within-component family on `C` only within-`C` edges — so this is the
    /// pre-existing behaviour on every complex with at most one family per pair, bit for bit.
    ///
    /// The 2-cell population is a **set of vertex triples**: a triple already carrying a face is
    /// never re-minted and its boundary coefficients are never added a second time. The returned
    /// ids are the faces this family stands over, newly founded or already standing, and they are
    /// recorded in [`Self::family_faces`] beside the family.
    fn found_faces_over(
        &mut self,
        steps: &[ConstraintVertexId],
        junctions: &[ConstraintVertexId],
        admitted: &BTreeSet<ConstraintEdge>,
    ) -> Result<Vec<ConstraintFaceId>, ConstraintError> {
        let mut standing: BTreeMap<[ConstraintVertexId; 3], ConstraintFaceId> = self
            .faces
            .values()
            .map(|face| (face.vertices, face.id))
            .collect();
        let mut owned = Vec::new();
        for step in steps.windows(2) {
            for junction in junctions {
                if *junction == step[0] || *junction == step[1] {
                    continue;
                }
                let first = ConstraintEdge::new(step[0], *junction)?.0;
                let second = ConstraintEdge::new(step[1], *junction)?.0;
                if admitted.contains(&first) && admitted.contains(&second) {
                    let triple = [step[0], step[1], *junction];
                    // A 2-cell is the triple, not the founding that reached it. A second family
                    // reaching the same triple stands over the same cell; it does not mint
                    // another, and it does not add the boundary a second time.
                    if let Some(existing) = standing.get(&triple) {
                        if !owned.contains(existing) {
                            owned.push(*existing);
                        }
                        continue;
                    }
                    let id = ConstraintFaceId(self.next_face);
                    self.next_face += 1;
                    let face = ConstraintFace {
                        id,
                        source_event: self.source_event,
                        vertices: triple,
                    };
                    for (edge, hand) in face.boundary()? {
                        *self.boundary.two_chain_boundary.entry(edge).or_default() +=
                            i64::from(hand);
                    }
                    self.faces.insert(id, face);
                    standing.insert(triple, id);
                    owned.push(id);
                }
            }
        }
        self.boundary
            .two_chain_boundary
            .retain(|_, hand| *hand != 0);
        Ok(owned)
    }

    pub fn component(
        &self,
        id: ConstraintComponentId,
    ) -> Result<&PresentedComponent, ConstraintError> {
        self.components
            .get(&id)
            .ok_or(ConstraintError::MissingComponent(id))
    }

    /// The first founded family addressed `left -> right`, in founding order.
    ///
    /// `left == right` addresses a [`ContactFamilyKind::WithinComponent`] family; when several
    /// were founded on that component — a second aperture, or a second declared separation — this
    /// returns the first, and [`Self::within_component_family`] names the separation as well. Each
    /// founding's own 2-cell population is [`Self::family_faces`] at that founding's index; the
    /// second founding neither re-mints a standing cell nor adds its boundary again.
    pub fn contact_family(
        &self,
        left: ConstraintComponentId,
        right: ConstraintComponentId,
    ) -> Result<&ContactFamily, ConstraintError> {
        self.contact_families
            .iter()
            .find(|family| family.left == left && family.right == right)
            .ok_or(ConstraintError::MissingContactFamily { left, right })
    }

    /// The 2-cells one founded family stands over, addressed by its founding index in
    /// [`Self::contact_families`].
    ///
    /// [definition] This is the **consumer semantics** a complex carrying several families needs:
    /// a family is graded against its own cells, not against the union. A cell two families both
    /// reach appears in both populations and is minted once.
    pub fn family_faces(&self, founding: usize) -> Option<&[ConstraintFaceId]> {
        self.family_faces.get(founding).map(Vec::as_slice)
    }

    /// The algebraic boundary of **one founded family's** 2-chain, recomputed from that family's
    /// own cells. [`ComplexBoundary::two_chain_boundary`] is the boundary of the whole 2-cell
    /// population; this is the boundary of one member of the family of complexes.
    pub fn two_chain_boundary_of_family(
        &self,
        founding: usize,
    ) -> Result<BTreeMap<ConstraintEdge, i64>, ConstraintError> {
        let population = self
            .family_faces
            .get(founding)
            .ok_or(ConstraintError::NoSuchFounding(founding))?;
        let mut boundary: BTreeMap<ConstraintEdge, i64> = BTreeMap::new();
        for id in population {
            let face = self
                .faces
                .get(id)
                .ok_or(ConstraintError::RemountedFaceMisaddressed(*id))?;
            for (edge, hand) in face.boundary()? {
                *boundary.entry(edge).or_default() += i64::from(hand);
            }
        }
        boundary.retain(|_, hand| *hand != 0);
        Ok(boundary)
    }

    /// The within-component family of one component at one declared sequence separation.
    pub fn within_component_family(
        &self,
        component: ConstraintComponentId,
        minimum_separation: u32,
    ) -> Result<&ContactFamily, ConstraintError> {
        self.contact_families
            .iter()
            .find(|family| {
                family.left == component
                    && family.right == component
                    && family.kind
                        == ContactFamilyKind::WithinComponent { minimum_separation }
            })
            .ok_or(ConstraintError::MissingContactFamily {
                left: component,
                right: component,
            })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactSeparator {
    pub left_primary_ordinal: u32,
    pub secondary_ordinal: u32,
    pub left_class: ContactClass,
    pub right_class: ContactClass,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossPresentationFibre {
    pub schema: String,
    pub component_sequence_kinship: Vec<(ConstraintComponentId, ConstraintComponentId)>,
    pub shared_inside: Vec<(u32, u32)>,
    pub shared_outside: Vec<(u32, u32)>,
    pub left_only_inside: Vec<(u32, u32)>,
    pub right_only_inside: Vec<(u32, u32)>,
    pub unresolved: Vec<(u32, u32, ContactClass, ContactClass)>,
    pub shortest_separator: Option<ContactSeparator>,
}

/// Compare one lineaged contact family across two distinct presentation occurrences. Component
/// sequence equality is checked as a kinship witness; it never identifies the occurrences.
pub fn cross_presentation_fibre(
    left_complex: &PhysicalConstraintComplex,
    right_complex: &PhysicalConstraintComplex,
    left_pair: (ConstraintComponentId, ConstraintComponentId),
    right_pair: (ConstraintComponentId, ConstraintComponentId),
) -> Result<CrossPresentationFibre, ConstraintError> {
    for (left, right) in [(left_pair.0, right_pair.0), (left_pair.1, right_pair.1)] {
        if left_complex.component(left)?.sequence != right_complex.component(right)?.sequence {
            return Err(ConstraintError::ComponentSequenceDisagrees { left, right });
        }
    }
    let left = left_complex.contact_family(left_pair.0, left_pair.1)?;
    let right = right_complex.contact_family(right_pair.0, right_pair.1)?;
    if left.readings.len() != right.readings.len() {
        return Err(ConstraintError::CrossPresentationPopulationDisagrees {
            left: left.readings.len(),
            right: right.readings.len(),
        });
    }
    let mut shared_inside = Vec::new();
    let mut shared_outside = Vec::new();
    let mut left_only_inside = Vec::new();
    let mut right_only_inside = Vec::new();
    let mut unresolved = Vec::new();
    let mut shortest_separator = None;
    for (a, b) in left.readings.iter().zip(&right.readings) {
        if (a.left_ordinal, a.right_ordinal) != (b.left_ordinal, b.right_ordinal) {
            return Err(ConstraintError::ContactOrderDisagrees);
        }
        let pair = (a.left_ordinal, a.right_ordinal);
        match (a.class, b.class) {
            (ContactClass::Inside, ContactClass::Inside) => shared_inside.push(pair),
            (ContactClass::Inside, ContactClass::Outside) => left_only_inside.push(pair),
            (ContactClass::Outside, ContactClass::Inside) => right_only_inside.push(pair),
            (ContactClass::Open, other) | (other, ContactClass::Open) => {
                unresolved.push((pair.0, pair.1, a.class, b.class));
                if other != ContactClass::Open && shortest_separator.is_none() {
                    shortest_separator = Some(ContactSeparator {
                        left_primary_ordinal: pair.0,
                        secondary_ordinal: pair.1,
                        left_class: a.class,
                        right_class: b.class,
                    });
                }
            }
            (ContactClass::Outside, ContactClass::Outside) => shared_outside.push(pair),
        }
        if a.class != b.class && shortest_separator.is_none() {
            shortest_separator = Some(ContactSeparator {
                left_primary_ordinal: pair.0,
                secondary_ordinal: pair.1,
                left_class: a.class,
                right_class: b.class,
            });
        }
    }
    Ok(CrossPresentationFibre {
        schema: "holonic-engine.cross-presentation-constraint-fibre.v1".to_owned(),
        component_sequence_kinship: vec![(left_pair.0, right_pair.0), (left_pair.1, right_pair.1)],
        shared_inside,
        shared_outside,
        left_only_inside,
        right_only_inside,
        unresolved,
        shortest_separator,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ConstraintError {
    #[error("component {0:?} is absent from this presentation")]
    MissingComponent(ConstraintComponentId),
    #[error("component {0} has no residue occurrences")]
    EmptyComponent(String),
    #[error("the edge collapses at vertex {0:?}")]
    CollapsedEdge(ConstraintVertexId),
    #[error(
        "the contact carrier returned {enacted} cells where the declared population has {expected}"
    )]
    ContactPopulationDisagrees { expected: usize, enacted: usize },
    #[error(
        "the uncertainty carrier returned {supplied} cells where the declared population has {expected}"
    )]
    UncertaintyPopulationDisagrees { expected: usize, supplied: usize },
    #[error("the contact carrier returned unknown class word {0}")]
    UnknownContactClass(u8),
    #[error("uncertainty is absent at contact pair {0:?}")]
    MissingUncertainty((u32, u32)),
    #[error(
        "the enacted contact at ({left_ordinal},{right_ordinal}) is {enacted:?}, but exact interval admission returns {exact:?}"
    )]
    CarrierDisagrees {
        left_ordinal: u32,
        right_ordinal: u32,
        enacted: ContactClass,
        exact: ContactClass,
    },
    #[error("contact family {left:?}->{right:?} is absent")]
    MissingContactFamily {
        left: ConstraintComponentId,
        right: ConstraintComponentId,
    },
    #[error("component kinship {left:?}->{right:?} is not witnessed by equal ordered monomers")]
    ComponentSequenceDisagrees {
        left: ConstraintComponentId,
        right: ConstraintComponentId,
    },
    #[error("cross-presentation contact populations differ: {left} versus {right}")]
    CrossPresentationPopulationDisagrees { left: usize, right: usize },
    #[error("the two contact populations are not in the same addressed pair order")]
    ContactOrderDisagrees,
    #[error(
        "a within-component family declares a sequence separation of {0}; separation 1 names the presented chain's own covalent step, which is a polygonal one-cell and not a contact, so the declaration must be at least 2 and this owner supplies no default"
    )]
    SeparationIsCovalent(u32),
    #[error("a contact family's kind disagrees with the components it names")]
    FamilyKindDisagreesWithItsComponents,
    #[error(
        "a component of extent {extent} overflows the machine integer counting its C(n − k + 1, 2) within-component pairs"
    )]
    WithinComponentPopulationOverflows { extent: usize },
    #[error("there is no founding at index {0}")]
    NoSuchFounding(usize),
    #[error("a remounted complex declares schema {0}, which this owner does not own")]
    RemountedSchemaMismatch(String),
    #[error("a remounted complex addresses occurrence {0:?} under another key")]
    RemountedVertexMisaddressed(ConstraintVertexId),
    #[error("a remounted complex names occurrence {0:?}, which it does not present")]
    RemountedVertexAbsent(ConstraintVertexId),
    #[error("a remounted complex addresses two-cell {0:?} under another key or past its counter")]
    RemountedFaceMisaddressed(ConstraintFaceId),
    #[error("a remounted complex carries two two-cells on the vertex triple {0:?}")]
    RemountedDuplicateFace([ConstraintVertexId; 3]),
    #[error("the two-cell on {0:?} has a boundary edge the remounted complex does not carry")]
    RemountedFaceEdgeAbsent([ConstraintVertexId; 3]),
    #[error(
        "a remounted complex's carried two-chain boundary is not the boundary recomputed from its own two-cells"
    )]
    RemountedBoundaryDisagrees,
    #[error("a remounted complex's two-chain boundary does not close: ∂∘∂ is nonzero")]
    RemountedBoundaryOfBoundaryNonzero,
    #[error(
        "a remounted complex carries {families} founded families and {populations} per-family two-cell populations"
    )]
    RemountedFamilyFacesMisaligned { families: usize, populations: usize },
}

#[cfg(test)]
#[path = "physical_constraint_complex/tests.rs"]
mod tests;
