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

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::EventId;
use crate::exact_value::ExactInterval;

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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContactFamily {
    pub left: ConstraintComponentId,
    pub right: ConstraintComponentId,
    pub aperture: DistanceAperture,
    /// The complete receiver population, including outside and open pairs.
    pub readings: Vec<ContactReading>,
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

#[derive(Debug, Serialize, Deserialize)]
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
    pub boundary: ComplexBoundary,
    next_face: u64,
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
            schema: "holonic-engine.physical-constraint-complex.v1".to_owned(),
            presentation_lineage: presentation_lineage.into(),
            source_event,
            components,
            vertices,
            polygonal_edges,
            contact_families: Vec::new(),
            contact_edges: BTreeSet::new(),
            faces: BTreeMap::new(),
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
                    self.contact_edges
                        .insert(ConstraintEdge::new(reading.left, reading.right)?.0);
                }
                readings.push(reading);
            }
        }

        // A higher cell is founded by actual incidence: one polygonal step and two admitted
        // contacts to the same junction. No display triangulation is promoted into topology.
        for left_pair in left_vertices.windows(2) {
            for right_vertex in &right_vertices {
                let first = ConstraintEdge::new(left_pair[0], *right_vertex)?.0;
                let second = ConstraintEdge::new(left_pair[1], *right_vertex)?.0;
                if self.contact_edges.contains(&first) && self.contact_edges.contains(&second) {
                    let id = ConstraintFaceId(self.next_face);
                    self.next_face += 1;
                    let face = ConstraintFace {
                        id,
                        source_event: self.source_event,
                        vertices: [left_pair[0], left_pair[1], *right_vertex],
                    };
                    for (edge, hand) in face.boundary()? {
                        *self.boundary.two_chain_boundary.entry(edge).or_default() +=
                            i64::from(hand);
                    }
                    self.faces.insert(id, face);
                }
            }
        }
        self.boundary
            .two_chain_boundary
            .retain(|_, hand| *hand != 0);
        self.contact_families.push(ContactFamily {
            left,
            right,
            aperture,
            readings,
        });
        Ok(())
    }

    pub fn component(
        &self,
        id: ConstraintComponentId,
    ) -> Result<&PresentedComponent, ConstraintError> {
        self.components
            .get(&id)
            .ok_or(ConstraintError::MissingComponent(id))
    }

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
}

#[cfg(test)]
#[path = "physical_constraint_complex/tests.rs"]
mod tests;
