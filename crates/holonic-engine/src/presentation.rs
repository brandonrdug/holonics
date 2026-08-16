//! Continuous plural receiver assembly and terminal finite presentation.
//!
//! Receiver faces are related by exact, caused projective maps.  Their
//! complete continuous primitives and crossing relations are assembled before
//! a platform boundary supplies a finite matrix.  A matrix member receives
//! every primitive whose support intersects its finite area; its center is
//! never used as a surrogate ray.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{FrameId, Rat, RatMat3, RatVec3, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ArrangementRelation, ArrangementSeam, CpuExecutionError, CpuExecutionReceipt, CpuExecutor,
    EventId, HomogeneousConic, ProjectedConic, ProjectedThread, ProjectedTriangle, ProjectiveLine2,
    ProjectiveLineFamily, ProjectivePoint2, ReceiverError, ReceiverFace, ReceiverPrimitive,
    ReceiverPrimitiveId, TransportedCoordinateField, canonical_homogeneous,
    indexed_arrangement_relations_with_cpu, linear_pieces,
};

/// One caused projective relation from a receiver face into the bounded
/// presentation face.  It is standing supplied by the active world, not an
/// arbitrary display placement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverStandingRelation {
    pub receiver: ReceiverId,
    pub source_event: EventId,
    pub into_presentation: RatMat3,
}

impl ReceiverStandingRelation {
    pub fn new(
        receiver: ReceiverId,
        source_event: EventId,
        into_presentation: RatMat3,
    ) -> Result<Self, PresentationError> {
        if into_presentation.determinant().is_zero() {
            return Err(PresentationError::SingularFaceRelation(receiver));
        }
        let entries = canonical_homogeneous([
            into_presentation.rows[0][0].clone(),
            into_presentation.rows[0][1].clone(),
            into_presentation.rows[0][2].clone(),
            into_presentation.rows[1][0].clone(),
            into_presentation.rows[1][1].clone(),
            into_presentation.rows[1][2].clone(),
            into_presentation.rows[2][0].clone(),
            into_presentation.rows[2][1].clone(),
            into_presentation.rows[2][2].clone(),
        ]);
        let into_presentation = RatMat3::new([
            [entries[0].clone(), entries[1].clone(), entries[2].clone()],
            [entries[3].clone(), entries[4].clone(), entries[5].clone()],
            [entries[6].clone(), entries[7].clone(), entries[8].clone()],
        ]);
        Ok(Self {
            receiver,
            source_event,
            into_presentation,
        })
    }

    pub fn identity(receiver: ReceiverId, source_event: EventId) -> Self {
        Self {
            receiver,
            source_event,
            into_presentation: RatMat3::identity(),
        }
    }

    pub fn push_point(&self, local: &ProjectivePoint2) -> ProjectivePoint2 {
        let result = self.into_presentation.apply(&RatVec3::new(
            local.x.clone(),
            local.y.clone(),
            local.w.clone(),
        ));
        ProjectivePoint2::new(result.x, result.y, result.z)
            .expect("an invertible standing relation cannot collapse a projective point")
    }

    pub fn pull_affine(&self, presentation: &[Rat; 2]) -> Option<[Rat; 2]> {
        let inverse = self.into_presentation.inverse()?;
        let local = inverse.apply(&RatVec3::new(
            presentation[0].clone(),
            presentation[1].clone(),
            Rat::one(),
        ));
        (!local.z.is_zero()).then(|| [&local.x / &local.z, &local.y / &local.z])
    }

    fn push_line(&self, line: &ProjectiveLine2) -> ProjectiveLine2 {
        let inverse_transpose = self
            .into_presentation
            .inverse()
            .expect("a standing receiver relation is invertible")
            .transpose();
        let line = inverse_transpose.apply(&RatVec3::new(
            line.a.clone(),
            line.b.clone(),
            line.c.clone(),
        ));
        ProjectiveLine2 {
            a: line.x,
            b: line.y,
            c: line.z,
        }
    }

    fn push_conic(&self, conic: &HomogeneousConic) -> Result<HomogeneousConic, PresentationError> {
        let inverse = self
            .into_presentation
            .inverse()
            .ok_or(PresentationError::SingularFaceRelation(self.receiver))?;
        Ok(HomogeneousConic::from_doubled_matrix(
            &inverse
                .transpose()
                .multiply(&conic.doubled_matrix())
                .multiply(&inverse),
        )?)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PluralReceiverAssembly {
    pub schema: String,
    pub boundary_name: String,
    pub faces: BTreeMap<ReceiverId, ReceiverFace>,
    pub relations: BTreeMap<ReceiverId, ReceiverStandingRelation>,
}

impl PluralReceiverAssembly {
    pub fn new(
        boundary_name: impl Into<String>,
        faces: Vec<ReceiverFace>,
        relations: Vec<ReceiverStandingRelation>,
    ) -> Result<Self, PresentationError> {
        if faces.is_empty() {
            return Err(PresentationError::EmptyAssembly);
        }
        let mut indexed_faces = BTreeMap::new();
        for face in faces {
            let receiver = face.receiver;
            if indexed_faces.insert(receiver, face).is_some() {
                return Err(PresentationError::DuplicateReceiver(receiver));
            }
        }
        let mut indexed_relations = BTreeMap::new();
        for relation in relations {
            let receiver = relation.receiver;
            if indexed_relations.insert(receiver, relation).is_some() {
                return Err(PresentationError::DuplicateRelation(receiver));
            }
        }
        let face_receivers = indexed_faces.keys().copied().collect::<BTreeSet<_>>();
        let relation_receivers = indexed_relations.keys().copied().collect::<BTreeSet<_>>();
        if face_receivers != relation_receivers {
            return Err(PresentationError::RelationPopulationMismatch {
                faces: face_receivers,
                relations: relation_receivers,
            });
        }
        Ok(Self {
            schema: "holonic-engine.plural-receiver-assembly.v2".to_owned(),
            boundary_name: boundary_name.into(),
            faces: indexed_faces,
            relations: indexed_relations,
        })
    }

    pub fn relation(
        &self,
        receiver: ReceiverId,
    ) -> Result<&ReceiverStandingRelation, PresentationError> {
        self.relations
            .get(&receiver)
            .ok_or(PresentationError::MissingReceiver(receiver))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentedPrimitive {
    pub receiver: ReceiverId,
    pub primitive: ReceiverPrimitive,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentedCoordinateField {
    pub receiver: ReceiverId,
    pub field: TransportedCoordinateField,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentedArrangementRelation {
    pub receiver_left: ReceiverId,
    pub receiver_right: ReceiverId,
    pub relation: ArrangementRelation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContinuousPresentation {
    pub schema: String,
    pub boundary_name: String,
    pub primitives: Vec<PresentedPrimitive>,
    pub coordinate_fields: Vec<PresentedCoordinateField>,
    pub relations: Vec<PresentedArrangementRelation>,
    pub seams: Vec<(ReceiverId, ArrangementSeam)>,
}

impl ContinuousPresentation {
    /// Form the finite-restriction input from an already selected population
    /// of exact presentation sections.  This does not assemble the complete
    /// plural crossing atlas and, crucially, does not transport any receiver
    /// which the caller did not select.
    pub(crate) fn selected_support(
        boundary_name: impl Into<String>,
        mut primitives: Vec<PresentedPrimitive>,
    ) -> Self {
        primitives.sort_by_key(|presented| (presented.receiver, presented.primitive.id()));
        Self {
            schema: "holonic-engine.selected-support-presentation.v1".to_owned(),
            boundary_name: boundary_name.into(),
            primitives,
            coordinate_fields: Vec::new(),
            relations: Vec::new(),
            seams: Vec::new(),
        }
    }
}

/// Materialize one receiver's local section through its contemporary exact
/// presentation relation.  Tube planning calls this only after structural
/// comparison proves that the prior presented section cannot carry.
pub(crate) fn materialize_receiver_support(
    face: &ReceiverFace,
    relation: &ReceiverStandingRelation,
) -> Result<Vec<PresentedPrimitive>, PresentationError> {
    if face.receiver != relation.receiver {
        return Err(PresentationError::RelationReceiverMismatch {
            face: face.receiver,
            relation: relation.receiver,
        });
    }
    face.arrangement
        .primitives
        .iter()
        .map(|primitive| {
            Ok(PresentedPrimitive {
                receiver: face.receiver,
                primitive: transform_primitive(primitive, relation)?,
            })
        })
        .collect()
}

pub fn assemble_presentation(
    assembly: &PluralReceiverAssembly,
) -> Result<ContinuousPresentation, PresentationError> {
    Ok(assemble_presentation_with_cpu(assembly, &CpuExecutor::serial())?.0)
}

pub fn assemble_presentation_with_cpu(
    assembly: &PluralReceiverAssembly,
    executor: &CpuExecutor,
) -> Result<(ContinuousPresentation, CpuExecutionReceipt), PresentationError> {
    assemble_presentation_selected(assembly, executor, true)
}

/// Transport the complete continuous support into the presentation chart
/// without deriving the independent all-crossings atlas. Finite aperture
/// support depends on these primitives, not on prior possession of every
/// pairwise relation witness.
pub fn assemble_support_presentation_with_cpu(
    assembly: &PluralReceiverAssembly,
    executor: &CpuExecutor,
) -> Result<(ContinuousPresentation, CpuExecutionReceipt), PresentationError> {
    assemble_presentation_selected(assembly, executor, false)
}

fn assemble_presentation_selected(
    assembly: &PluralReceiverAssembly,
    executor: &CpuExecutor,
    form_crossing_atlas: bool,
) -> Result<(ContinuousPresentation, CpuExecutionReceipt), PresentationError> {
    let mut primitives = Vec::new();
    let mut coordinate_fields = Vec::new();
    let mut seams = Vec::new();
    for (receiver, face) in &assembly.faces {
        let relation = assembly.relation(*receiver)?;
        for primitive in &face.arrangement.primitives {
            primitives.push(PresentedPrimitive {
                receiver: *receiver,
                primitive: transform_primitive(primitive, relation)?,
            });
        }
        for field in &face.arrangement.coordinate_fields {
            coordinate_fields.push(PresentedCoordinateField {
                receiver: *receiver,
                field: TransportedCoordinateField {
                    source_frame: field.source_frame,
                    first_axis: transform_line_family(&field.first_axis, relation),
                    second_axis: transform_line_family(&field.second_axis, relation),
                },
            });
        }
        seams.extend(
            face.arrangement
                .seams
                .iter()
                .cloned()
                .map(|seam| (*receiver, seam)),
        );
    }
    primitives.sort_by_key(|presented| (presented.receiver, presented.primitive.id()));

    if !form_crossing_atlas {
        let (_, execution) = executor
            .execute_indexed(
                &[] as &[()],
                |_index, _input| Ok::<_, PresentationError>(()),
            )
            .map_err(|error| match error {
                CpuExecutionError::Operation(error) => error,
                CpuExecutionError::WorkerPanicked => PresentationError::WorkerPanicked,
            })?;
        return Ok((
            ContinuousPresentation {
                schema: "holonic-engine.continuous-support-presentation.v1".to_owned(),
                boundary_name: assembly.boundary_name.clone(),
                primitives,
                coordinate_fields,
                relations: Vec::new(),
                seams,
            },
            execution,
        ));
    }

    let local_relations_reusable = assembly
        .relations
        .values()
        .all(|relation| relation.into_presentation == RatMat3::identity());
    let mut relations = if local_relations_reusable {
        assembly
            .faces
            .iter()
            .flat_map(|(receiver, face)| {
                face.arrangement.relations.iter().cloned().map(|relation| {
                    PresentedArrangementRelation {
                        receiver_left: *receiver,
                        receiver_right: *receiver,
                        relation,
                    }
                })
            })
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };

    // Form the transported arrangement once. The former pair wrapper rebuilt
    // each primitive's own edges for every neighbour, duplicated internal
    // crossings, and then mislabeled those duplicates as relations between
    // the wrapper's two receivers. Instance ordinals retain receiver identity
    // even when the same source primitive appears in plural receiver charts.
    let mut indexed_linear = Vec::new();
    let mut indexed_conics = Vec::new();
    for (ordinal, presented) in primitives.iter().enumerate() {
        match &presented.primitive {
            ReceiverPrimitive::Conic(conic) => indexed_conics.push((ordinal, conic)),
            _ => {
                let mut primitive_seams = Vec::new();
                indexed_linear.extend(
                    linear_pieces(
                        std::slice::from_ref(&presented.primitive),
                        &mut primitive_seams,
                    )
                    .into_iter()
                    .map(|piece| (ordinal, piece)),
                );
                seams.extend(
                    primitive_seams
                        .into_iter()
                        .map(|seam| (presented.receiver, seam)),
                );
            }
        }
    }
    let primitive_receivers = primitives
        .iter()
        .map(|primitive| primitive.receiver)
        .collect::<Vec<_>>();
    let (indexed_relations, execution) = indexed_arrangement_relations_with_cpu(
        &indexed_linear,
        &indexed_conics,
        local_relations_reusable.then_some(primitive_receivers.as_slice()),
        executor,
    )
    .map_err(PresentationError::Receiver)?;
    relations.extend(indexed_relations.into_iter().map(
        |(left_primitive, right_primitive, relation)| PresentedArrangementRelation {
            receiver_left: primitives[left_primitive].receiver,
            receiver_right: primitives[right_primitive].receiver,
            relation,
        },
    ));
    Ok((
        ContinuousPresentation {
            schema: "holonic-engine.continuous-presentation.v1".to_owned(),
            boundary_name: assembly.boundary_name.clone(),
            primitives,
            coordinate_fields,
            relations,
            seams,
        },
        execution,
    ))
}

fn transform_line_family(
    family: &ProjectiveLineFamily,
    relation: &ReceiverStandingRelation,
) -> ProjectiveLineFamily {
    ProjectiveLineFamily {
        zero: relation.push_line(&family.zero),
        coefficient: relation.push_line(&family.coefficient),
    }
}

fn transform_primitive(
    primitive: &ReceiverPrimitive,
    relation: &ReceiverStandingRelation,
) -> Result<ReceiverPrimitive, PresentationError> {
    Ok(match primitive {
        ReceiverPrimitive::Triangle(triangle) => ReceiverPrimitive::Triangle(ProjectedTriangle {
            source: triangle.source,
            vertices: triangle
                .vertices
                .clone()
                .map(|point| relation.push_point(&point)),
            receiver_depths: triangle.receiver_depths.clone(),
            receiver_depth: triangle.receiver_depth.as_ref().map(|depth| {
                Box::new(crate::ProjectiveDepthLaw {
                    numerator: relation.push_line(&depth.numerator),
                    denominator: relation.push_line(&depth.denominator),
                })
            }),
        }),
        ReceiverPrimitive::Thread(thread) => ReceiverPrimitive::Thread(ProjectedThread {
            source: thread.source,
            vertices: thread
                .vertices
                .iter()
                .map(|point| relation.push_point(point))
                .collect(),
            receiver_depths: thread.receiver_depths.clone(),
            closed: thread.closed,
        }),
        ReceiverPrimitive::Conic(conic) => {
            let form = relation.push_conic(&conic.form)?;
            ReceiverPrimitive::Conic(ProjectedConic {
                source: conic.source,
                class_in_receiver_chart: form.classify(),
                form,
                receiver_depth: crate::ProjectiveDepthLaw {
                    numerator: relation.push_line(&conic.receiver_depth.numerator),
                    denominator: relation.push_line(&conic.receiver_depth.denominator),
                },
            })
        }
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PresentationAddress {
    pub column: u32,
    pub row: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentationBoundary {
    pub horizontal_span: Rat,
    pub vertical_span: Rat,
}

impl PresentationBoundary {
    fn validate(&self) -> Result<(), PresentationError> {
        if !self.horizontal_span.is_positive() || !self.vertical_span.is_positive() {
            return Err(PresentationError::InvalidPresentationBoundary);
        }
        Ok(())
    }
}

/// The finite matrix exists only at this terminal platform boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TerminalMatrixSpec {
    pub width: u32,
    pub height: u32,
    pub boundary: PresentationBoundary,
}

impl TerminalMatrixSpec {
    pub fn validate(&self) -> Result<(), PresentationError> {
        if self.width == 0 || self.height == 0 {
            return Err(PresentationError::EmptyResolution);
        }
        self.boundary.validate()
    }

    pub fn addresses(&self) -> Result<Vec<PresentationAddress>, PresentationError> {
        self.validate()?;
        Ok((0..self.height)
            .flat_map(|row| (0..self.width).map(move |column| PresentationAddress { column, row }))
            .collect())
    }

    pub fn cell(&self, address: PresentationAddress) -> Result<ExactCell, PresentationError> {
        self.validate()?;
        if address.column >= self.width || address.row >= self.height {
            return Err(PresentationError::AddressOutsideResolution(address));
        }
        let two = Rat::from_integer(2.into());
        let width = Rat::from_integer(self.width.into());
        let height = Rat::from_integer(self.height.into());
        let horizontal_half = &self.boundary.horizontal_span / &two;
        let vertical_half = &self.boundary.vertical_span / two;
        let left = -&horizontal_half
            + Rat::from_integer(address.column.into()) * &self.boundary.horizontal_span / &width;
        let right = -&horizontal_half
            + Rat::from_integer((address.column + 1).into()) * &self.boundary.horizontal_span
                / width;
        let top = &vertical_half
            - Rat::from_integer(address.row.into()) * &self.boundary.vertical_span / &height;
        let bottom = &vertical_half
            - Rat::from_integer((address.row + 1).into()) * &self.boundary.vertical_span / height;
        Ok(ExactCell {
            lower: [left, bottom],
            upper: [right, top],
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCell {
    pub lower: [Rat; 2],
    pub upper: [Rat; 2],
}

impl ExactCell {
    pub fn corners(&self) -> [[Rat; 2]; 4] {
        [
            [self.lower[0].clone(), self.lower[1].clone()],
            [self.upper[0].clone(), self.lower[1].clone()],
            [self.upper[0].clone(), self.upper[1].clone()],
            [self.lower[0].clone(), self.upper[1].clone()],
        ]
    }

    fn contains(&self, point: &[Rat; 2]) -> bool {
        point[0] >= self.lower[0]
            && point[0] <= self.upper[0]
            && point[1] >= self.lower[1]
            && point[1] <= self.upper[1]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactCellSupport {
    Interior,
    Boundary,
    OpenProjective,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveContribution {
    pub receiver: ReceiverId,
    pub primitive: ReceiverPrimitiveId,
    pub support: ExactCellSupport,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinateFieldContribution {
    pub receiver: ReceiverId,
    pub source_frame: FrameId,
    pub first_axis: IntegralPhaseCell,
    pub second_axis: IntegralPhaseCell,
}

/// Exact integral level testimony for one continuous local phase field over
/// one finite terminal member.
///
/// `Levels` means every integer in the inclusive interval is attained in the
/// member. `OpenProjective` means the phase denominator crosses zero there,
/// so no finite integer interval may replace that seam.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IntegralPhaseCell {
    NoLevel,
    Levels { first: BigInt, last: BigInt },
    OpenProjective,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticPhaseContribution {
    pub receiver: ReceiverId,
    pub primitive: ReceiverPrimitiveId,
    pub levels: IntegralPhaseCell,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DepthPhaseContribution {
    pub receiver: ReceiverId,
    pub primitive: ReceiverPrimitiveId,
    pub levels: IntegralPhaseCell,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentationMember {
    pub address: PresentationAddress,
    pub cell: ExactCell,
    pub primitives: Vec<PrimitiveContribution>,
    pub coordinate_fields: Vec<CoordinateFieldContribution>,
    pub quadratic_phases: Vec<QuadraticPhaseContribution>,
    pub depth_phases: Vec<DepthPhaseContribution>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentationWork {
    pub addresses: BigUint,
    pub primitive_cell_classifications: BigUint,
    pub coordinate_field_restrictions: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentationMatrix {
    pub schema: String,
    pub assembly_name: String,
    pub specification: TerminalMatrixSpec,
    pub members: Vec<PresentationMember>,
    pub work: PresentationWork,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExecutedPresentation {
    pub continuous: ContinuousPresentation,
    pub matrix: PresentationMatrix,
    pub arrangement_execution: CpuExecutionReceipt,
    pub execution: CpuExecutionReceipt,
}

pub fn classify_presentation_address(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    address: PresentationAddress,
) -> Result<PresentationMember, PresentationError> {
    classify_address_for_receiver(presentation, specification, address, None)
}

pub fn classify_receiver_address(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receiver: ReceiverId,
    address: PresentationAddress,
) -> Result<PresentationMember, PresentationError> {
    classify_address_for_receiver(presentation, specification, address, Some(receiver))
}

/// The finite address trace cast by one receiver's continuous primitive
/// arrangement into a terminal aperture.
///
/// This is support-driven: exact simplex edges and conic zero loci select the
/// bounded members they cross. The terminal matrix does not search every
/// address and does not supply adjacency to the causal world.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PresentedPrimitiveKey {
    pub receiver: ReceiverId,
    pub primitive: ReceiverPrimitiveId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveApertureTrace {
    pub key: PresentedPrimitiveKey,
    pub addresses: BTreeSet<PresentationAddress>,
    pub exact_support_queries: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverApertureTrace {
    pub schema: String,
    pub receiver: ReceiverId,
    /// Exact restriction retained at the same structural grain at which the
    /// continuous presentation was formed.
    #[serde(default)]
    pub primitive_sections: BTreeMap<ReceiverPrimitiveId, PrimitiveApertureTrace>,
    /// Aggregate receiver support derived from `primitive_sections`.
    pub addresses: BTreeSet<PresentationAddress>,
    pub support_multiplicity: BTreeMap<PresentationAddress, BigUint>,
    pub primitive_traces: BigUint,
    pub exact_support_queries: BigUint,
}

impl ReceiverApertureTrace {
    /// Exact boundary equality independent of executor work testimony.
    ///
    /// `exact_support_queries` may differ between recursive cpu refinement
    /// and tiled device classification. It is a cost receipt, not part of the
    /// finite support standing.
    pub fn has_same_exact_support(&self, other: &Self) -> bool {
        self.receiver == other.receiver
            && self.addresses == other.addresses
            && self.support_multiplicity == other.support_multiplicity
            && self.primitive_traces == other.primitive_traces
            && self.primitive_sections.len() == other.primitive_sections.len()
            && self.primitive_sections.iter().all(|(primitive, section)| {
                other
                    .primitive_sections
                    .get(primitive)
                    .is_some_and(|other| {
                        section.key == other.key && section.addresses == other.addresses
                    })
            })
    }

    pub fn from_primitive_sections(
        receiver: ReceiverId,
        sections: impl IntoIterator<Item = PrimitiveApertureTrace>,
    ) -> Result<Self, PresentationError> {
        let mut primitive_sections = BTreeMap::new();
        for section in sections {
            if section.key.receiver != receiver {
                return Err(PresentationError::MisaddressedPrimitiveTrace {
                    expected: receiver,
                    actual: section.key.receiver,
                });
            }
            if primitive_sections
                .insert(section.key.primitive, section)
                .is_some()
            {
                return Err(PresentationError::DuplicatePrimitiveTrace(receiver));
            }
        }
        let mut addresses = BTreeSet::new();
        let mut support_multiplicity = BTreeMap::new();
        let mut exact_support_queries = BigUint::zero();
        for section in primitive_sections.values() {
            exact_support_queries += &section.exact_support_queries;
            for address in &section.addresses {
                addresses.insert(*address);
                *support_multiplicity
                    .entry(*address)
                    .or_insert_with(BigUint::zero) += BigUint::one();
            }
        }
        Ok(Self {
            schema: "holonic-engine.receiver-aperture-trace.v2".to_owned(),
            receiver,
            primitive_traces: BigUint::from(primitive_sections.len()),
            primitive_sections,
            addresses,
            support_multiplicity,
            exact_support_queries,
        })
    }

    pub fn empty(receiver: ReceiverId) -> Self {
        Self::from_primitive_sections(receiver, std::iter::empty())
            .expect("an empty primitive population is well addressed")
    }
}

struct ExactApertureGrid {
    horizontal: Vec<Rat>,
    vertical: Vec<Rat>,
}

impl ExactApertureGrid {
    fn new(specification: &TerminalMatrixSpec) -> Self {
        let two = Rat::from_integer(2.into());
        let horizontal_half = &specification.boundary.horizontal_span / &two;
        let vertical_half = &specification.boundary.vertical_span / two;
        let horizontal_step =
            &specification.boundary.horizontal_span / Rat::from_integer(specification.width.into());
        let vertical_step =
            &specification.boundary.vertical_span / Rat::from_integer(specification.height.into());
        Self {
            horizontal: (0..=specification.width)
                .map(|column| {
                    -&horizontal_half + Rat::from_integer(column.into()) * &horizontal_step
                })
                .collect(),
            vertical: (0..=specification.height)
                .map(|row| &vertical_half - Rat::from_integer(row.into()) * &vertical_step)
                .collect(),
        }
    }
}

/// Substitute the terminal aperture chart into one exact conic and clear all
/// coefficient denominators once. The returned integer quadratic is
/// sign-equivalent to the source conic at every terminal coordinate.
pub(crate) fn terminal_integer_conic_coefficients(
    form: &HomogeneousConic,
    specification: &TerminalMatrixSpec,
) -> Result<[BigInt; 6], PresentationError> {
    specification.validate()?;
    let two = Rat::from_integer(2.into());
    let horizontal_step =
        &specification.boundary.horizontal_span / Rat::from_integer(specification.width.into());
    let horizontal_origin = -&specification.boundary.horizontal_span / &two;
    let vertical_step =
        -&specification.boundary.vertical_span / Rat::from_integer(specification.height.into());
    let vertical_origin = &specification.boundary.vertical_span / two;
    let coefficients = [
        &form.xx * &horizontal_step * &horizontal_step,
        &form.xy * &horizontal_step * &vertical_step,
        &form.yy * &vertical_step * &vertical_step,
        Rat::from_integer(2.into()) * &form.xx * &horizontal_step * &horizontal_origin
            + &form.xy * &horizontal_step * &vertical_origin
            + &form.xw * &horizontal_step,
        &form.xy * &horizontal_origin * &vertical_step
            + Rat::from_integer(2.into()) * &form.yy * &vertical_step * &vertical_origin
            + &form.yw * &vertical_step,
        &form.xx * &horizontal_origin * &horizontal_origin
            + &form.xy * &horizontal_origin * &vertical_origin
            + &form.yy * &vertical_origin * &vertical_origin
            + &form.xw * &horizontal_origin
            + &form.yw * &vertical_origin
            + &form.ww,
    ];
    let common_denominator = coefficients
        .iter()
        .fold(BigInt::from(1_u8), |common, coefficient| {
            let denominator = coefficient.denom().clone();
            let divisor = integer_gcd(common.clone(), denominator.clone());
            common / divisor * denominator
        });
    let mut integer = coefficients
        .map(|coefficient| coefficient.numer() * (&common_denominator / coefficient.denom()));
    let content = integer
        .iter()
        .filter(|coefficient| !coefficient.is_zero())
        .map(Signed::abs)
        .reduce(integer_gcd)
        .unwrap_or_else(|| BigInt::from(1_u8));
    for coefficient in &mut integer {
        *coefficient /= &content;
    }
    Ok(integer)
}

fn integer_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

#[derive(Clone)]
struct ExactGridRatio {
    numerator: BigInt,
    denominator: BigInt,
}

impl ExactGridRatio {
    fn new(mut numerator: BigInt, mut denominator: BigInt) -> Option<Self> {
        if denominator.is_zero() {
            return None;
        }
        if denominator.is_negative() {
            numerator = -numerator;
            denominator = -denominator;
        }
        Some(Self {
            numerator,
            denominator,
        })
    }

    fn integer(value: u32) -> Self {
        Self {
            numerator: BigInt::from(value),
            denominator: BigInt::one(),
        }
    }

    fn lies_between(&self, lower: u32, upper: u32) -> bool {
        self.numerator >= BigInt::from(lower) * &self.denominator
            && self.numerator <= BigInt::from(upper) * &self.denominator
    }
}

/// One exact terminal-coordinate conic. The chart substitution, denominator
/// clearing, stationary coordinates, and their signs are formed once per
/// primitive rather than once per visited aperture region.
struct ExactTerminalConic {
    coefficients: [BigInt; 6],
    vertical_stationary: Vec<Option<(ExactGridRatio, BigInt)>>,
    horizontal_stationary: Vec<Option<(ExactGridRatio, BigInt)>>,
    interior_stationary: Option<(ExactGridRatio, ExactGridRatio, BigInt)>,
}

impl ExactTerminalConic {
    fn new(
        form: &HomogeneousConic,
        specification: &TerminalMatrixSpec,
    ) -> Result<Self, PresentationError> {
        let coefficients = terminal_integer_conic_coefficients(form, specification)?;
        let [xx, xy, yy, x, y, _] = coefficients.each_ref();
        let two = BigInt::from(2_u8);
        let vertical_stationary = (0..=specification.width)
            .map(|column| {
                let column = BigInt::from(column);
                let coordinate = ExactGridRatio::new(-(xy * &column + y), &two * yy)?;
                let value = evaluate_integer_conic(
                    &coefficients,
                    &ExactGridRatio {
                        numerator: column,
                        denominator: BigInt::one(),
                    },
                    &coordinate,
                );
                Some((coordinate, value))
            })
            .collect();
        let horizontal_stationary = (0..=specification.height)
            .map(|row| {
                let row = BigInt::from(row);
                let coordinate = ExactGridRatio::new(-(xy * &row + x), &two * xx)?;
                let value = evaluate_integer_conic(
                    &coefficients,
                    &coordinate,
                    &ExactGridRatio {
                        numerator: row,
                        denominator: BigInt::one(),
                    },
                );
                Some((coordinate, value))
            })
            .collect();
        let determinant = &two * xx * &two * yy - xy * xy;
        let interior_stationary = ExactGridRatio::new(xy * y - &two * yy * x, determinant.clone())
            .zip(ExactGridRatio::new(xy * x - &two * xx * y, determinant))
            .map(|(horizontal, vertical)| {
                let value = evaluate_integer_conic(&coefficients, &horizontal, &vertical);
                (horizontal, vertical, value)
            });
        Ok(Self {
            coefficients,
            vertical_stationary,
            horizontal_stationary,
            interior_stationary,
        })
    }

    fn crosses(&self, region: ApertureRegion) -> bool {
        let mut negative = false;
        let mut positive = false;
        let mut observe = |value: &BigInt| {
            if value.is_zero() {
                return true;
            }
            negative |= value.is_negative();
            positive |= value.is_positive();
            negative && positive
        };
        for (horizontal, vertical) in [
            (region.left, region.top),
            (region.right, region.top),
            (region.right, region.bottom),
            (region.left, region.bottom),
        ] {
            if observe(&evaluate_integer_conic(
                &self.coefficients,
                &ExactGridRatio::integer(horizontal),
                &ExactGridRatio::integer(vertical),
            )) {
                return true;
            }
        }
        for column in [region.left, region.right] {
            if let Some((coordinate, value)) = &self.vertical_stationary
                [usize::try_from(column).expect("terminal column fits memory")]
                && coordinate.lies_between(region.top, region.bottom)
                && observe(value)
            {
                return true;
            }
        }
        for row in [region.top, region.bottom] {
            if let Some((coordinate, value)) =
                &self.horizontal_stationary[usize::try_from(row).expect("terminal row fits memory")]
                && coordinate.lies_between(region.left, region.right)
                && observe(value)
            {
                return true;
            }
        }
        if let Some((horizontal, vertical, value)) = &self.interior_stationary
            && horizontal.lies_between(region.left, region.right)
            && vertical.lies_between(region.top, region.bottom)
            && observe(value)
        {
            return true;
        }
        negative && positive
    }
}

/// Evaluate an integer quadratic at two exact rational terminal coordinates.
/// The returned integer is the rational value multiplied by the positive
/// square of both denominators, so its sign is exact.
fn evaluate_integer_conic(
    coefficients: &[BigInt; 6],
    horizontal: &ExactGridRatio,
    vertical: &ExactGridRatio,
) -> BigInt {
    let [xx, xy, yy, x, y, constant] = coefficients.each_ref();
    let horizontal_square = &horizontal.denominator * &horizontal.denominator;
    let vertical_square = &vertical.denominator * &vertical.denominator;
    xx * &horizontal.numerator * &horizontal.numerator * &vertical_square
        + xy * &horizontal.numerator
            * &vertical.numerator
            * &horizontal.denominator
            * &vertical.denominator
        + yy * &vertical.numerator * &vertical.numerator * &horizontal_square
        + x * &horizontal.numerator * &horizontal.denominator * &vertical_square
        + y * &vertical.numerator * &vertical.denominator * &horizontal_square
        + constant * horizontal_square * vertical_square
}

/// One finite boundary difference in the terminal aperture. The region is
/// half-open in address space, but its exact geometric carrier includes both
/// outer boundaries. Subdivision is an observation procedure only; it is not
/// a chronology or neighborhood relation in the source world.
#[derive(Clone, Copy)]
struct ApertureRegion {
    left: u32,
    right: u32,
    top: u32,
    bottom: u32,
}

impl ApertureRegion {
    fn complete(specification: &TerminalMatrixSpec) -> Self {
        Self {
            left: 0,
            right: specification.width,
            top: 0,
            bottom: specification.height,
        }
    }

    fn exact_cell(self, grid: &ExactApertureGrid) -> ExactCell {
        let left = usize::try_from(self.left).expect("a bounded column fits memory");
        let right = usize::try_from(self.right).expect("a bounded column fits memory");
        let top = usize::try_from(self.top).expect("a bounded row fits memory");
        let bottom = usize::try_from(self.bottom).expect("a bounded row fits memory");
        ExactCell {
            lower: [grid.horizontal[left].clone(), grid.vertical[bottom].clone()],
            upper: [grid.horizontal[right].clone(), grid.vertical[top].clone()],
        }
    }

    fn address(self) -> Option<PresentationAddress> {
        (self.right - self.left == 1 && self.bottom - self.top == 1).then_some(
            PresentationAddress {
                column: self.left,
                row: self.top,
            },
        )
    }

    fn divide(self) -> Vec<Self> {
        let horizontal = self.right - self.left;
        let vertical = self.bottom - self.top;
        if horizontal == 1 && vertical == 1 {
            return Vec::new();
        }
        if horizontal >= vertical && horizontal > 1 {
            let middle = self.left + horizontal / 2;
            vec![
                Self {
                    right: middle,
                    ..self
                },
                Self {
                    left: middle,
                    ..self
                },
            ]
        } else {
            let middle = self.top + vertical / 2;
            vec![
                Self {
                    bottom: middle,
                    ..self
                },
                Self {
                    top: middle,
                    ..self
                },
            ]
        }
    }
}

pub fn trace_receiver_aperture(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receiver: ReceiverId,
) -> Result<ReceiverApertureTrace, PresentationError> {
    Ok(trace_receivers_aperture_with_cpu(
        presentation,
        specification,
        &BTreeSet::from([receiver]),
        &CpuExecutor::serial(),
    )?
    .0
    .remove(&receiver)
    .expect("the requested receiver trace was admitted"))
}

pub fn trace_receivers_aperture_with_cpu(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    executor: &CpuExecutor,
) -> Result<
    (
        BTreeMap<ReceiverId, ReceiverApertureTrace>,
        CpuExecutionReceipt,
    ),
    PresentationError,
> {
    trace_receivers_aperture_species_with_cpu(
        presentation,
        specification,
        receivers,
        executor,
        true,
        true,
    )
}

/// Complete arbitrary-rational reference authority retained to grade the
/// denominator-cleared integer terminal carrier.
pub fn trace_receivers_aperture_with_rational_conic_authority(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    executor: &CpuExecutor,
) -> Result<
    (
        BTreeMap<ReceiverId, ReceiverApertureTrace>,
        CpuExecutionReceipt,
    ),
    PresentationError,
> {
    trace_receivers_aperture_species_with_cpu(
        presentation,
        specification,
        receivers,
        executor,
        true,
        false,
    )
}

/// Restrict only linear simplex/thread supports. This is the exact cpu
/// companion to a device which realizes conic support directly.
pub fn trace_receivers_linear_aperture_with_cpu(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    executor: &CpuExecutor,
) -> Result<
    (
        BTreeMap<ReceiverId, ReceiverApertureTrace>,
        CpuExecutionReceipt,
    ),
    PresentationError,
> {
    trace_receivers_aperture_species_with_cpu(
        presentation,
        specification,
        receivers,
        executor,
        false,
        true,
    )
}

fn trace_receivers_aperture_species_with_cpu(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    executor: &CpuExecutor,
    include_conics: bool,
    integer_conics: bool,
) -> Result<
    (
        BTreeMap<ReceiverId, ReceiverApertureTrace>,
        CpuExecutionReceipt,
    ),
    PresentationError,
> {
    let keys = presentation
        .primitives
        .iter()
        .filter(|presented| {
            receivers.contains(&presented.receiver)
                && (include_conics || !matches!(presented.primitive, ReceiverPrimitive::Conic(_)))
        })
        .map(|presented| PresentedPrimitiveKey {
            receiver: presented.receiver,
            primitive: presented.primitive.id(),
        })
        .collect::<BTreeSet<_>>();
    let (primitive_traces, execution) = trace_primitive_species_aperture_with_cpu(
        presentation,
        specification,
        &keys,
        executor,
        integer_conics,
    )?;
    let mut by_receiver = receivers
        .iter()
        .copied()
        .map(|receiver| (receiver, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for trace in primitive_traces.into_values() {
        by_receiver
            .get_mut(&trace.key.receiver)
            .expect("every traced primitive belongs to an admitted receiver")
            .push(trace);
    }
    let traces = by_receiver
        .into_iter()
        .map(|(receiver, sections)| {
            Ok((
                receiver,
                ReceiverApertureTrace::from_primitive_sections(receiver, sections)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, PresentationError>>()?;
    Ok((traces, execution))
}

/// Restrict exactly the requested structural primitive population.
///
/// This is the terminal companion to the receiver-tube atlas: unchanged
/// primitive sections can remain standing while only changed keys descend to
/// finite addresses.
pub fn trace_primitives_aperture_with_cpu(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    primitives: &BTreeSet<PresentedPrimitiveKey>,
    executor: &CpuExecutor,
) -> Result<
    (
        BTreeMap<PresentedPrimitiveKey, PrimitiveApertureTrace>,
        CpuExecutionReceipt,
    ),
    PresentationError,
> {
    trace_primitive_species_aperture_with_cpu(
        presentation,
        specification,
        primitives,
        executor,
        true,
    )
}

fn trace_primitive_species_aperture_with_cpu(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    requested: &BTreeSet<PresentedPrimitiveKey>,
    executor: &CpuExecutor,
    integer_conics: bool,
) -> Result<
    (
        BTreeMap<PresentedPrimitiveKey, PrimitiveApertureTrace>,
        CpuExecutionReceipt,
    ),
    PresentationError,
> {
    specification.validate()?;
    let grid = ExactApertureGrid::new(specification);
    let primitives = presentation
        .primitives
        .iter()
        .filter(|presented| {
            requested.contains(&PresentedPrimitiveKey {
                receiver: presented.receiver,
                primitive: presented.primitive.id(),
            })
        })
        .collect::<Vec<_>>();
    let selected = primitives
        .iter()
        .map(|presented| PresentedPrimitiveKey {
            receiver: presented.receiver,
            primitive: presented.primitive.id(),
        })
        .collect::<BTreeSet<_>>();
    if &selected != requested {
        return Err(PresentationError::PrimitiveTracePopulationMismatch {
            requested: requested.clone(),
            selected,
        });
    }
    let (partial, execution) = executor
        .execute_indexed(&primitives, |_index, presented| {
            let mut addresses = BTreeSet::new();
            let mut exact_support_queries = 0_u64;
            trace_presented_primitive(
                &presented.primitive,
                specification,
                &grid,
                &mut addresses,
                &mut exact_support_queries,
                integer_conics,
            )?;
            Ok::<_, PresentationError>(PrimitiveApertureTrace {
                key: PresentedPrimitiveKey {
                    receiver: presented.receiver,
                    primitive: presented.primitive.id(),
                },
                addresses,
                exact_support_queries: BigUint::from(exact_support_queries),
            })
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => PresentationError::WorkerPanicked,
        })?;
    let mut traces = BTreeMap::new();
    for trace in partial {
        let key = trace.key;
        if traces.insert(key, trace).is_some() {
            return Err(PresentationError::DuplicatePrimitiveTrace(key.receiver));
        }
    }
    Ok((traces, execution))
}

fn trace_presented_primitive(
    primitive: &ReceiverPrimitive,
    specification: &TerminalMatrixSpec,
    grid: &ExactApertureGrid,
    addresses: &mut BTreeSet<PresentationAddress>,
    exact_support_queries: &mut u64,
    integer_terminal_carriers: bool,
) -> Result<(), PresentationError> {
    match primitive {
        ReceiverPrimitive::Triangle(triangle) => {
            for edge in triangle.vertices.windows(2) {
                trace_segment_support(
                    &edge[0],
                    &edge[1],
                    specification,
                    grid,
                    addresses,
                    exact_support_queries,
                    integer_terminal_carriers,
                )?;
            }
            trace_segment_support(
                &triangle.vertices[2],
                &triangle.vertices[0],
                specification,
                grid,
                addresses,
                exact_support_queries,
                integer_terminal_carriers,
            )?;
        }
        ReceiverPrimitive::Thread(thread) => {
            for edge in thread.vertices.windows(2) {
                trace_segment_support(
                    &edge[0],
                    &edge[1],
                    specification,
                    grid,
                    addresses,
                    exact_support_queries,
                    integer_terminal_carriers,
                )?;
            }
            if thread.closed && thread.vertices.len() > 1 {
                trace_segment_support(
                    thread.vertices.last().expect("a closed thread has a tail"),
                    &thread.vertices[0],
                    specification,
                    grid,
                    addresses,
                    exact_support_queries,
                    integer_terminal_carriers,
                )?;
            }
        }
        ReceiverPrimitive::Conic(conic) => {
            if integer_terminal_carriers {
                trace_conic_support(&conic.form, specification, addresses, exact_support_queries)?;
            } else {
                trace_conic_support_rational(
                    &conic.form,
                    specification,
                    grid,
                    addresses,
                    exact_support_queries,
                );
            }
        }
    }
    Ok(())
}

fn trace_segment_support(
    start: &ProjectivePoint2,
    end: &ProjectivePoint2,
    specification: &TerminalMatrixSpec,
    grid: &ExactApertureGrid,
    addresses: &mut BTreeSet<PresentationAddress>,
    exact_support_queries: &mut u64,
    integer_terminal_carrier: bool,
) -> Result<(), PresentationError> {
    if integer_terminal_carrier {
        trace_projective_segment(start, end, specification, addresses, exact_support_queries);
    } else {
        trace_projective_segment_rational(
            start,
            end,
            specification,
            grid,
            addresses,
            exact_support_queries,
        )?;
    }
    Ok(())
}

fn trace_projective_segment(
    start: &ProjectivePoint2,
    end: &ProjectivePoint2,
    specification: &TerminalMatrixSpec,
    addresses: &mut BTreeSet<PresentationAddress>,
    exact_support_queries: &mut u64,
) {
    for (finite_start, finite_end) in terminal_projective_segments(start, end, specification) {
        let mut regions = vec![ApertureRegion::complete(specification)];
        while let Some(region) = regions.pop() {
            *exact_support_queries += 1;
            if !terminal_segment_intersects_region(&finite_start, &finite_end, region) {
                continue;
            }
            if let Some(address) = region.address() {
                addresses.insert(address);
            } else {
                regions.extend(region.divide());
            }
        }
    }
}

fn trace_projective_segment_rational(
    start: &ProjectivePoint2,
    end: &ProjectivePoint2,
    specification: &TerminalMatrixSpec,
    grid: &ExactApertureGrid,
    addresses: &mut BTreeSet<PresentationAddress>,
    exact_support_queries: &mut u64,
) -> Result<(), PresentationError> {
    for (finite_start, finite_end) in clip_projective_segment_to_aperture(start, end, specification)
    {
        let mut regions = vec![ApertureRegion::complete(specification)];
        while let Some(region) = regions.pop() {
            *exact_support_queries += 1;
            let cell = region.exact_cell(grid);
            if !segment_intersects_cell(&finite_start, &finite_end, &cell) {
                continue;
            }
            if let Some(address) = region.address() {
                addresses.insert(address);
            } else {
                regions.extend(region.divide());
            }
        }
    }
    Ok(())
}

pub(crate) fn terminal_projective_segments(
    start: &ProjectivePoint2,
    end: &ProjectivePoint2,
    specification: &TerminalMatrixSpec,
) -> Vec<([BigInt; 3], [BigInt; 3])> {
    let two = Rat::from_integer(2.into());
    let terminal = |point: &[Rat; 2]| {
        [
            (&point[0] + &specification.boundary.horizontal_span / &two)
                * Rat::from_integer(specification.width.into())
                / &specification.boundary.horizontal_span,
            (&specification.boundary.vertical_span / &two - &point[1])
                * Rat::from_integer(specification.height.into())
                / &specification.boundary.vertical_span,
        ]
    };
    clip_projective_segment_to_aperture(start, end, specification)
        .into_iter()
        .map(|(first, second)| {
            (
                homogeneous_terminal_point(&terminal(&first)),
                homogeneous_terminal_point(&terminal(&second)),
            )
        })
        .collect()
}

pub(crate) fn homogeneous_terminal_point(point: &[Rat; 2]) -> [BigInt; 3] {
    let divisor = integer_gcd(point[0].denom().clone(), point[1].denom().clone());
    let common = point[0].denom() / &divisor * point[1].denom();
    let mut homogeneous = [
        point[0].numer() * (&common / point[0].denom()),
        point[1].numer() * (&common / point[1].denom()),
        common,
    ];
    let content = homogeneous
        .iter()
        .map(Signed::abs)
        .reduce(integer_gcd)
        .unwrap_or_else(|| BigInt::from(1_u8));
    for coordinate in &mut homogeneous {
        *coordinate /= &content;
    }
    if homogeneous[2].is_negative() {
        for coordinate in &mut homogeneous {
            *coordinate = -coordinate.clone();
        }
    }
    homogeneous
}

fn terminal_segment_intersects_region(
    start: &[BigInt; 3],
    end: &[BigInt; 3],
    region: ApertureRegion,
) -> bool {
    if terminal_point_in_region(start, region) || terminal_point_in_region(end, region) {
        return true;
    }
    let corners = [
        terminal_integer_point(region.left, region.top),
        terminal_integer_point(region.right, region.top),
        terminal_integer_point(region.right, region.bottom),
        terminal_integer_point(region.left, region.bottom),
    ];
    corners
        .iter()
        .zip(corners.iter().cycle().skip(1))
        .take(corners.len())
        .any(|(first, second)| terminal_segments_intersect(start, end, first, second))
}

fn terminal_integer_point(horizontal: u32, vertical: u32) -> [BigInt; 3] {
    [
        BigInt::from(horizontal),
        BigInt::from(vertical),
        BigInt::one(),
    ]
}

fn terminal_point_in_region(point: &[BigInt; 3], region: ApertureRegion) -> bool {
    point[0] >= BigInt::from(region.left) * &point[2]
        && point[0] <= BigInt::from(region.right) * &point[2]
        && point[1] >= BigInt::from(region.top) * &point[2]
        && point[1] <= BigInt::from(region.bottom) * &point[2]
}

fn terminal_segments_intersect(
    a: &[BigInt; 3],
    b: &[BigInt; 3],
    c: &[BigInt; 3],
    d: &[BigInt; 3],
) -> bool {
    let abc = terminal_orientation(a, b, c);
    let abd = terminal_orientation(a, b, d);
    let cda = terminal_orientation(c, d, a);
    let cdb = terminal_orientation(c, d, b);
    if opposite_signs(&abc, &abd) && opposite_signs(&cda, &cdb) {
        return true;
    }
    (abc.is_zero() && terminal_point_between(a, b, c))
        || (abd.is_zero() && terminal_point_between(a, b, d))
        || (cda.is_zero() && terminal_point_between(c, d, a))
        || (cdb.is_zero() && terminal_point_between(c, d, b))
}

fn terminal_orientation(first: &[BigInt; 3], second: &[BigInt; 3], third: &[BigInt; 3]) -> BigInt {
    &first[0] * (&second[1] * &third[2] - &second[2] * &third[1])
        - &first[1] * (&second[0] * &third[2] - &second[2] * &third[0])
        + &first[2] * (&second[0] * &third[1] - &second[1] * &third[0])
}

fn opposite_signs(left: &BigInt, right: &BigInt) -> bool {
    (left.is_negative() && right.is_positive()) || (left.is_positive() && right.is_negative())
}

fn terminal_point_between(first: &[BigInt; 3], second: &[BigInt; 3], point: &[BigInt; 3]) -> bool {
    terminal_axis_between(first, second, point, 0) && terminal_axis_between(first, second, point, 1)
}

fn terminal_axis_between(
    first: &[BigInt; 3],
    second: &[BigInt; 3],
    point: &[BigInt; 3],
    axis: usize,
) -> bool {
    let first_to_second = (&first[axis] * &second[2]).cmp(&(&second[axis] * &first[2]));
    let first_to_point = (&first[axis] * &point[2]).cmp(&(&point[axis] * &first[2]));
    let point_to_second = (&point[axis] * &second[2]).cmp(&(&second[axis] * &point[2]));
    match first_to_second {
        std::cmp::Ordering::Less | std::cmp::Ordering::Equal => {
            first_to_point != std::cmp::Ordering::Greater
                && point_to_second != std::cmp::Ordering::Greater
        }
        std::cmp::Ordering::Greater => {
            first_to_point != std::cmp::Ordering::Less
                && point_to_second != std::cmp::Ordering::Less
        }
    }
}

/// Restrict the caused projective word
/// `p(t)=(1-t) start + t end`, `0<=t<=1`, to the finite receiver aperture.
///
/// `w=0` is a projective horizon, not a large coordinate. If the word crosses
/// that horizon, its affine trace has two opposed branches. Each branch is
/// clipped independently by exact linear inequalities and only its finite
/// boundary difference is returned.
pub(crate) fn clip_projective_segment_to_aperture(
    start: &ProjectivePoint2,
    end: &ProjectivePoint2,
    specification: &TerminalMatrixSpec,
) -> Vec<([Rat; 2], [Rat; 2])> {
    let two = Rat::from_integer(2.into());
    let lower = [
        -&specification.boundary.horizontal_span / &two,
        -&specification.boundary.vertical_span / &two,
    ];
    let upper = [
        &specification.boundary.horizontal_span / &two,
        &specification.boundary.vertical_span / two,
    ];
    let difference = [&end.x - &start.x, &end.y - &start.y, &end.w - &start.w];
    let mut cuts = vec![Rat::zero(), Rat::one()];
    if !difference[2].is_zero() {
        let horizon = -&start.w / &difference[2];
        if horizon > Rat::zero() && horizon < Rat::one() {
            cuts.push(horizon);
        }
    }
    cuts.sort();
    cuts.dedup();

    let coordinate = |axis: usize, parameter: &Rat| {
        let origin = match axis {
            0 => &start.x,
            1 => &start.y,
            _ => &start.w,
        };
        origin + &difference[axis] * parameter
    };
    let mut pieces = Vec::new();
    for interval in cuts.windows(2) {
        let mut entered = interval[0].clone();
        let mut departed = interval[1].clone();
        if entered == departed {
            continue;
        }
        let midpoint = (&entered + &departed) / Rat::from_integer(2.into());
        let horizon_hand = coordinate(2, &midpoint);
        let hand = if horizon_hand.is_positive() {
            Rat::one()
        } else if horizon_hand.is_negative() {
            -Rat::one()
        } else {
            continue;
        };
        let mut admitted = true;
        for axis in 0..2 {
            let origin = if axis == 0 { &start.x } else { &start.y };
            let delta = &difference[axis];
            let inequalities = [
                (
                    &hand * (origin - &lower[axis] * &start.w),
                    &hand * (delta - &lower[axis] * &difference[2]),
                ),
                (
                    &hand * (&upper[axis] * &start.w - origin),
                    &hand * (&upper[axis] * &difference[2] - delta),
                ),
            ];
            for (constant, coefficient) in inequalities {
                if coefficient.is_zero() {
                    admitted &= !constant.is_negative();
                } else {
                    let crossing = -constant / &coefficient;
                    if coefficient.is_positive() {
                        entered = std::cmp::max(entered, crossing);
                    } else {
                        departed = std::cmp::min(departed, crossing);
                    }
                }
                if !admitted || entered > departed {
                    break;
                }
            }
            if !admitted || entered > departed {
                break;
            }
        }
        if !admitted || entered > departed {
            continue;
        }
        let affine = |parameter: &Rat| {
            let w = coordinate(2, parameter);
            (!w.is_zero()).then(|| [coordinate(0, parameter) / &w, coordinate(1, parameter) / w])
        };
        if let (Some(first), Some(last)) = (affine(&entered), affine(&departed)) {
            pieces.push((first, last));
        }
    }
    pieces
}

fn trace_conic_support(
    form: &HomogeneousConic,
    specification: &TerminalMatrixSpec,
    addresses: &mut BTreeSet<PresentationAddress>,
    exact_support_queries: &mut u64,
) -> Result<(), PresentationError> {
    let terminal = ExactTerminalConic::new(form, specification)?;
    let mut regions = vec![ApertureRegion::complete(specification)];
    while let Some(region) = regions.pop() {
        *exact_support_queries += 1;
        if !terminal.crosses(region) {
            continue;
        }
        if let Some(address) = region.address() {
            addresses.insert(address);
        } else {
            regions.extend(region.divide());
        }
    }
    Ok(())
}

fn trace_conic_support_rational(
    form: &HomogeneousConic,
    specification: &TerminalMatrixSpec,
    grid: &ExactApertureGrid,
    addresses: &mut BTreeSet<PresentationAddress>,
    exact_support_queries: &mut u64,
) {
    let mut regions = vec![ApertureRegion::complete(specification)];
    while let Some(region) = regions.pop() {
        *exact_support_queries += 1;
        if !conic_crosses_cell(form, &region.exact_cell(grid)) {
            continue;
        }
        if let Some(address) = region.address() {
            addresses.insert(address);
        } else {
            regions.extend(region.divide());
        }
    }
}

fn conic_crosses_cell(form: &HomogeneousConic, cell: &ExactCell) -> bool {
    quadratic_range(form, cell)
        .as_ref()
        .and_then(zero_support)
        .is_some()
}

fn classify_address_for_receiver(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    address: PresentationAddress,
    receiver: Option<ReceiverId>,
) -> Result<PresentationMember, PresentationError> {
    let cell = specification.cell(address)?;
    Ok(classify_presentation_cell(
        presentation,
        address,
        cell,
        receiver,
    ))
}

fn classify_presentation_cell(
    presentation: &ContinuousPresentation,
    address: PresentationAddress,
    cell: ExactCell,
    receiver: Option<ReceiverId>,
) -> PresentationMember {
    let mut primitives = Vec::new();
    let mut quadratic_phases = Vec::new();
    let mut depth_phases = Vec::new();
    for presented in presentation
        .primitives
        .iter()
        .filter(|presented| receiver.is_none_or(|receiver| presented.receiver == receiver))
    {
        let support = primitive_cell_support(&presented.primitive, &cell);
        if let ReceiverPrimitive::Conic(conic) = &presented.primitive {
            let range = quadratic_range(&conic.form, &cell);
            if let Some((minimum, maximum)) = &range {
                quadratic_phases.push(QuadraticPhaseContribution {
                    receiver: presented.receiver,
                    primitive: conic.source,
                    levels: integral_span(minimum, maximum),
                });
            }
        }
        if let Some(support) = support {
            primitives.push(PrimitiveContribution {
                receiver: presented.receiver,
                primitive: presented.primitive.id(),
                support,
            });
            let depth = match &presented.primitive {
                ReceiverPrimitive::Triangle(triangle) => {
                    triangle.receiver_depth.as_ref().map(Box::as_ref)
                }
                ReceiverPrimitive::Conic(conic) => Some(&conic.receiver_depth),
                ReceiverPrimitive::Thread(_) => None,
            };
            if let Some(depth) = depth {
                depth_phases.push(DepthPhaseContribution {
                    receiver: presented.receiver,
                    primitive: presented.primitive.id(),
                    levels: rational_linear_phase(depth, &cell),
                });
            }
        }
    }
    let coordinate_fields = presentation
        .coordinate_fields
        .iter()
        .filter(|field| receiver.is_none_or(|receiver| field.receiver == receiver))
        .map(|field| CoordinateFieldContribution {
            receiver: field.receiver,
            source_frame: field.field.source_frame,
            first_axis: integral_line_family_span(&field.field.first_axis, &cell),
            second_axis: integral_line_family_span(&field.field.second_axis, &cell),
        })
        .collect();
    PresentationMember {
        address,
        cell,
        primitives,
        coordinate_fields,
        quadratic_phases,
        depth_phases,
    }
}

pub fn quotient_presentation(
    assembly: &PluralReceiverAssembly,
    specification: &TerminalMatrixSpec,
    executor: &CpuExecutor,
) -> Result<ExecutedPresentation, PresentationError> {
    let (continuous, arrangement_execution) = assemble_presentation_with_cpu(assembly, executor)?;
    let addresses = specification.addresses()?;
    let (members, execution) = executor
        .execute_indexed(&addresses, |_index, address| {
            classify_presentation_address(&continuous, specification, *address)
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => PresentationError::WorkerPanicked,
        })?;
    Ok(ExecutedPresentation {
        matrix: PresentationMatrix {
            schema: "holonic-engine.terminal-presentation-matrix.v2".to_owned(),
            assembly_name: assembly.boundary_name.clone(),
            specification: specification.clone(),
            members,
            work: PresentationWork {
                addresses: BigUint::from(addresses.len()),
                primitive_cell_classifications: BigUint::from(
                    addresses.len() * continuous.primitives.len(),
                ),
                coordinate_field_restrictions: BigUint::from(
                    addresses.len() * continuous.coordinate_fields.len(),
                ),
            },
        },
        continuous,
        arrangement_execution,
        execution,
    })
}

fn primitive_cell_support(
    primitive: &ReceiverPrimitive,
    cell: &ExactCell,
) -> Option<ExactCellSupport> {
    match primitive {
        ReceiverPrimitive::Triangle(triangle) => polygon_support(&triangle.vertices, true, cell),
        ReceiverPrimitive::Thread(thread) => polygon_support(&thread.vertices, thread.closed, cell),
        ReceiverPrimitive::Conic(conic) => quadratic_range(&conic.form, cell)
            .as_ref()
            .and_then(zero_support),
    }
}

fn polygon_support(
    points: &[ProjectivePoint2],
    closed: bool,
    cell: &ExactCell,
) -> Option<ExactCellSupport> {
    let Some(affine) = points
        .iter()
        .map(ProjectivePoint2::affine)
        .collect::<Option<Vec<_>>>()
    else {
        return Some(ExactCellSupport::OpenProjective);
    };
    if affine.iter().any(|point| cell.contains(point)) {
        return Some(ExactCellSupport::Interior);
    }
    let edge_count = affine.len().saturating_sub(1) + usize::from(closed && affine.len() > 1);
    for ordinal in 0..edge_count {
        if segment_intersects_cell(
            &affine[ordinal],
            &affine[(ordinal + 1) % affine.len()],
            cell,
        ) {
            return Some(ExactCellSupport::Boundary);
        }
    }
    if closed
        && affine.len() >= 3
        && cell
            .corners()
            .iter()
            .any(|corner| point_in_polygon(corner, &affine))
    {
        return Some(ExactCellSupport::Interior);
    }
    None
}

fn segment_intersects_cell(start: &[Rat; 2], end: &[Rat; 2], cell: &ExactCell) -> bool {
    if cell.contains(start) || cell.contains(end) {
        return true;
    }
    let corners = cell.corners();
    (0..4).any(|index| segments_intersect(start, end, &corners[index], &corners[(index + 1) % 4]))
}

fn orientation(a: &[Rat; 2], b: &[Rat; 2], c: &[Rat; 2]) -> Rat {
    (&b[0] - &a[0]) * (&c[1] - &a[1]) - (&b[1] - &a[1]) * (&c[0] - &a[0])
}

fn on_segment(a: &[Rat; 2], b: &[Rat; 2], point: &[Rat; 2]) -> bool {
    orientation(a, b, point).is_zero()
        && point[0] >= std::cmp::min(a[0].clone(), b[0].clone())
        && point[0] <= std::cmp::max(a[0].clone(), b[0].clone())
        && point[1] >= std::cmp::min(a[1].clone(), b[1].clone())
        && point[1] <= std::cmp::max(a[1].clone(), b[1].clone())
}

fn segments_intersect(a: &[Rat; 2], b: &[Rat; 2], c: &[Rat; 2], d: &[Rat; 2]) -> bool {
    let first = orientation(a, b, c);
    let second = orientation(a, b, d);
    let third = orientation(c, d, a);
    let fourth = orientation(c, d, b);
    (first.is_positive() != second.is_positive()
        && third.is_positive() != fourth.is_positive()
        && !first.is_zero()
        && !second.is_zero()
        && !third.is_zero()
        && !fourth.is_zero())
        || on_segment(a, b, c)
        || on_segment(a, b, d)
        || on_segment(c, d, a)
        || on_segment(c, d, b)
}

fn point_in_polygon(point: &[Rat; 2], polygon: &[[Rat; 2]]) -> bool {
    // Convexity is not assumed.  Exact winding parity uses horizontal ray
    // crossings; boundary is admitted directly.
    let mut inside = false;
    for index in 0..polygon.len() {
        let left = &polygon[index];
        let right = &polygon[(index + 1) % polygon.len()];
        if on_segment(left, right, point) {
            return true;
        }
        let crosses = (left[1] > point[1]) != (right[1] > point[1]);
        if crosses {
            let x =
                &left[0] + (&point[1] - &left[1]) * (&right[0] - &left[0]) / (&right[1] - &left[1]);
            if x > point[0] {
                inside = !inside;
            }
        }
    }
    inside
}

/// A quadratic reaches its extrema on a rectangle at a corner, a stationary
/// point on an edge, or an interior stationary point.  All candidates are
/// rational for a rational quadratic, so conic/cell support is exact.
fn quadratic_range(form: &HomogeneousConic, cell: &ExactCell) -> Option<(Rat, Rat)> {
    let mut candidates = cell.corners().to_vec();
    for x in [&cell.lower[0], &cell.upper[0]] {
        let denominator = Rat::from_integer(2.into()) * &form.yy;
        if !denominator.is_zero() {
            let y = -(&form.xy * x + &form.yw) / denominator;
            if y >= cell.lower[1] && y <= cell.upper[1] {
                candidates.push([x.clone(), y]);
            }
        }
    }
    for y in [&cell.lower[1], &cell.upper[1]] {
        let denominator = Rat::from_integer(2.into()) * &form.xx;
        if !denominator.is_zero() {
            let x = -(&form.xy * y + &form.xw) / denominator;
            if x >= cell.lower[0] && x <= cell.upper[0] {
                candidates.push([x, y.clone()]);
            }
        }
    }
    let two = Rat::from_integer(2.into());
    let determinant = &two * &form.xx * &two * &form.yy - &form.xy * &form.xy;
    if !determinant.is_zero() {
        let x = (-&form.xw * &two * &form.yy + &form.xy * &form.yw) / &determinant;
        let y = (-&two * &form.xx * &form.yw + &form.xy * &form.xw) / determinant;
        if cell.contains(&[x.clone(), y.clone()]) {
            candidates.push([x, y]);
        }
    }
    let values = candidates
        .iter()
        .map(|point| form.evaluate(&[point[0].clone(), point[1].clone(), Rat::one()]))
        .collect::<Vec<_>>();
    Some((values.iter().min()?.clone(), values.iter().max()?.clone()))
}

fn zero_support(range: &(Rat, Rat)) -> Option<ExactCellSupport> {
    let (minimum, maximum) = range;
    if minimum > &Rat::zero() || maximum < &Rat::zero() {
        None
    } else if minimum.is_zero() || maximum.is_zero() {
        Some(ExactCellSupport::Boundary)
    } else {
        Some(ExactCellSupport::Interior)
    }
}

fn integral_line_family_span(family: &ProjectiveLineFamily, cell: &ExactCell) -> IntegralPhaseCell {
    let values = cell
        .corners()
        .map(|point| {
            let homogeneous = [point[0].clone(), point[1].clone(), Rat::one()];
            let evaluate = |line: &ProjectiveLine2| {
                &line.a * &homogeneous[0] + &line.b * &homogeneous[1] + &line.c * &homogeneous[2]
            };
            let denominator = evaluate(&family.coefficient);
            let numerator = -evaluate(&family.zero);
            (numerator, denominator)
        })
        .to_vec();
    let denominator_positive = values
        .iter()
        .all(|(_, denominator)| denominator.is_positive());
    let denominator_negative = values
        .iter()
        .all(|(_, denominator)| denominator.is_negative());
    if !denominator_positive && !denominator_negative {
        return IntegralPhaseCell::OpenProjective;
    }
    let phases = values
        .into_iter()
        .map(|(numerator, denominator)| numerator / denominator)
        .collect::<Vec<_>>();
    integral_span(
        phases.iter().min().expect("a finite cell has four corners"),
        phases.iter().max().expect("a finite cell has four corners"),
    )
}

fn rational_linear_phase(law: &crate::ProjectiveDepthLaw, cell: &ExactCell) -> IntegralPhaseCell {
    let values = cell
        .corners()
        .map(|point| {
            let homogeneous = [point[0].clone(), point[1].clone(), Rat::one()];
            let evaluate = |line: &ProjectiveLine2| {
                &line.a * &homogeneous[0] + &line.b * &homogeneous[1] + &line.c
            };
            (evaluate(&law.numerator), evaluate(&law.denominator))
        })
        .to_vec();
    let denominator_positive = values
        .iter()
        .all(|(_, denominator)| denominator.is_positive());
    let denominator_negative = values
        .iter()
        .all(|(_, denominator)| denominator.is_negative());
    if !denominator_positive && !denominator_negative {
        return IntegralPhaseCell::OpenProjective;
    }
    let depths = values
        .into_iter()
        .map(|(numerator, denominator)| numerator / denominator)
        .collect::<Vec<_>>();
    integral_span(
        depths
            .iter()
            .min()
            .expect("a finite cell has four depth corners"),
        depths
            .iter()
            .max()
            .expect("a finite cell has four depth corners"),
    )
}

fn integral_span(minimum: &Rat, maximum: &Rat) -> IntegralPhaseCell {
    let first = ceil_rational(minimum);
    let last = floor_rational(maximum);
    if first <= last {
        IntegralPhaseCell::Levels { first, last }
    } else {
        IntegralPhaseCell::NoLevel
    }
}

fn floor_rational(value: &Rat) -> BigInt {
    let quotient = value.numer() / value.denom();
    let remainder = value.numer() % value.denom();
    if value.is_negative() && !remainder.is_zero() {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

fn ceil_rational(value: &Rat) -> BigInt {
    -floor_rational(&-value)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PresentationError {
    #[error("receiver {0:?} has a singular standing face relation")]
    SingularFaceRelation(ReceiverId),
    #[error("a bounded plural presentation requires at least one receiver face")]
    EmptyAssembly,
    #[error("receiver {0:?} occurs more than once")]
    DuplicateReceiver(ReceiverId),
    #[error("receiver {0:?} has more than one standing relation")]
    DuplicateRelation(ReceiverId),
    #[error("receiver face and standing-relation populations differ")]
    RelationPopulationMismatch {
        faces: BTreeSet<ReceiverId>,
        relations: BTreeSet<ReceiverId>,
    },
    #[error(
        "receiver face {face:?} cannot be transported by receiver {relation:?}'s standing relation"
    )]
    RelationReceiverMismatch {
        face: ReceiverId,
        relation: ReceiverId,
    },
    #[error("receiver {0:?} is not part of this bounded presentation")]
    MissingReceiver(ReceiverId),
    #[error("a finite presentation matrix must have nonzero width and height")]
    EmptyResolution,
    #[error("presentation spans must be positive")]
    InvalidPresentationBoundary,
    #[error("address {0:?} lies outside the terminal matrix")]
    AddressOutsideResolution(PresentationAddress),
    #[error("one physical presentation worker panicked")]
    WorkerPanicked,
    #[error("receiver {0:?} returned more than one terminal trace for one primitive identity")]
    DuplicatePrimitiveTrace(ReceiverId),
    #[error("primitive trace was addressed to receiver {actual:?}, expected receiver {expected:?}")]
    MisaddressedPrimitiveTrace {
        expected: ReceiverId,
        actual: ReceiverId,
    },
    #[error("requested and selected terminal primitive populations differ")]
    PrimitiveTracePopulationMismatch {
        requested: BTreeSet<PresentedPrimitiveKey>,
        selected: BTreeSet<PresentedPrimitiveKey>,
    },
    #[error(transparent)]
    Receiver(#[from] ReceiverError),
    #[error(transparent)]
    Conic(#[from] crate::ConicError),
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use relational_geometry::{Construction, Geometry, ProjectionLaw, Receiver, integer};

    use super::*;
    use crate::{RayFamily, ReceiverFaceExtent, ReceiverFaceSpec, receive_face};

    #[test]
    fn exact_support_equality_excludes_executor_work_testimony() {
        let receiver = ReceiverId(91);
        let primitive = ReceiverPrimitiveId::NativeConic(crate::ConicCellId(4));
        let address = PresentationAddress { column: 2, row: 3 };
        let trace = |address, queries| {
            ReceiverApertureTrace::from_primitive_sections(
                receiver,
                [PrimitiveApertureTrace {
                    key: PresentedPrimitiveKey {
                        receiver,
                        primitive,
                    },
                    addresses: BTreeSet::from([address]),
                    exact_support_queries: BigUint::from(queries),
                }],
            )
            .unwrap()
        };
        let cpu = trace(address, 17_u8);
        let device = trace(address, 41_u8);
        assert_ne!(cpu, device);
        assert!(cpu.has_same_exact_support(&device));
        assert!(
            !cpu.has_same_exact_support(&trace(PresentationAddress { column: 3, row: 3 }, 17_u8,))
        );
    }

    fn assembly() -> PluralReceiverAssembly {
        let (mut construction, frame) = Construction::new("source");
        construction
            .add_entity(
                "large triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-2, -2, 2),
                        RatVec3::from_i64(2, -2, 2),
                        RatVec3::from_i64(0, 2, 2),
                    ],
                },
            )
            .unwrap();
        let spec = |id| ReceiverFaceSpec {
            receiver: Receiver::new(
                ReceiverId(id),
                "receiver",
                frame,
                ProjectionLaw::PerspectiveRay {
                    focal_distance: integer(1),
                },
            ),
            extent: ReceiverFaceExtent {
                horizontal_span: integer(3),
                vertical_span: integer(2),
            },
            rays: RayFamily::Central {
                center: RatVec3::zero(),
                forward: RatVec3::from_i64(0, 0, 1),
                horizontal: RatVec3::from_i64(1, 0, 0),
                vertical: RatVec3::from_i64(0, 1, 0),
            },
            acceptance: None,
        };
        let left = receive_face(&construction, &spec(1)).unwrap();
        let right = receive_face(&construction, &spec(2)).unwrap();
        PluralReceiverAssembly::new(
            "caused pair",
            vec![left, right],
            vec![
                ReceiverStandingRelation::identity(ReceiverId(1), EventId(1)),
                ReceiverStandingRelation::new(
                    ReceiverId(2),
                    EventId(2),
                    RatMat3::from_i64([[1, 0, 1], [0, 1, 0], [0, 0, 1]]),
                )
                .unwrap(),
            ],
        )
        .unwrap()
    }

    fn terminal() -> TerminalMatrixSpec {
        TerminalMatrixSpec {
            width: 11,
            height: 7,
            boundary: PresentationBoundary {
                horizontal_span: integer(4),
                vertical_span: integer(3),
            },
        }
    }

    #[test]
    fn continuous_assembly_precedes_area_classification() {
        let assembly = assembly();
        let executed =
            quotient_presentation(&assembly, &terminal(), &CpuExecutor::serial()).unwrap();
        assert_eq!(executed.continuous.primitives.len(), 2);
        assert!(
            executed
                .matrix
                .members
                .iter()
                .any(|member| member.primitives.len() == 2)
        );
        let center = executed
            .matrix
            .members
            .iter()
            .find(|member| member.address == PresentationAddress { column: 5, row: 3 })
            .expect("the terminal matrix carries its center member");
        assert!(!center.depth_phases.is_empty());
        assert!(center.depth_phases.iter().all(|phase| {
            phase.levels
                == IntegralPhaseCell::Levels {
                    first: BigInt::from(2),
                    last: BigInt::from(2),
                }
        }));
    }

    #[test]
    fn serial_and_multicore_terminal_quotients_are_identical() {
        let assembly = assembly();
        let serial = quotient_presentation(&assembly, &terminal(), &CpuExecutor::serial()).unwrap();
        let parallel = quotient_presentation(
            &assembly,
            &terminal(),
            &CpuExecutor::multicore(NonZeroUsize::new(4).unwrap()),
        )
        .unwrap();
        assert_eq!(serial.continuous, parallel.continuous);
        assert_eq!(serial.matrix, parallel.matrix);
        assert_ne!(serial.execution, parallel.execution);
    }

    #[test]
    fn aperture_trace_follows_simplex_support_without_scanning_the_matrix() {
        let continuous = assemble_presentation(&assembly()).unwrap();
        let trace = trace_receiver_aperture(&continuous, &terminal(), ReceiverId(1)).unwrap();
        assert!(!trace.addresses.is_empty());
        assert!(
            trace.addresses.len()
                < usize::try_from(terminal().width * terminal().height)
                    .expect("the test matrix is bounded")
        );
        assert_eq!(trace.primitive_traces, BigUint::from(1_u8));
        assert!(trace.exact_support_queries >= BigUint::from(trace.addresses.len()));
    }

    #[test]
    fn a_projective_edge_crossing_infinity_casts_two_finite_aperture_branches() {
        let start = ProjectivePoint2::new(integer(-1), integer(0), integer(1)).unwrap();
        let end = ProjectivePoint2::new(integer(-1), integer(0), integer(-1)).unwrap();
        let pieces = clip_projective_segment_to_aperture(&start, &end, &terminal());
        assert_eq!(pieces.len(), 2);
        let mut horizontal = pieces
            .into_iter()
            .flat_map(|(first, last)| [first[0].clone(), last[0].clone()])
            .collect::<Vec<_>>();
        horizontal.sort();
        assert_eq!(
            horizontal,
            vec![integer(-2), integer(-1), integer(1), integer(2)]
        );
    }

    #[test]
    fn integral_span_is_exact_across_negative_and_positive_boundaries() {
        assert_eq!(
            integral_span(
                &relational_geometry::rat(-21, 5),
                &relational_geometry::rat(29, 5)
            ),
            IntegralPhaseCell::Levels {
                first: BigInt::from(-4),
                last: BigInt::from(5),
            }
        );
        assert_eq!(
            integral_span(
                &relational_geometry::rat(1, 5),
                &relational_geometry::rat(4, 5)
            ),
            IntegralPhaseCell::NoLevel
        );
    }

    #[test]
    fn coordinate_phase_has_no_authored_finite_level_cutoff() {
        let family = ProjectiveLineFamily {
            zero: ProjectiveLine2 {
                a: integer(1),
                b: Rat::zero(),
                c: Rat::zero(),
            },
            coefficient: ProjectiveLine2 {
                a: Rat::zero(),
                b: Rat::zero(),
                c: integer(-1),
            },
        };
        let cell = ExactCell {
            lower: [integer(20), integer(-1)],
            upper: [integer(21), integer(1)],
        };

        assert_eq!(
            integral_line_family_span(&family, &cell),
            IntegralPhaseCell::Levels {
                first: BigInt::from(20),
                last: BigInt::from(21),
            }
        );
    }

    #[test]
    fn quadratic_phase_exposes_curved_levels_beyond_zero_contour() {
        let circle_levels = HomogeneousConic::new([
            integer(1),
            Rat::zero(),
            integer(1),
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
        ])
        .unwrap();
        let cell = ExactCell {
            lower: [integer(3), integer(4)],
            upper: [integer(4), integer(5)],
        };
        let range = quadratic_range(&circle_levels, &cell).unwrap();

        assert_eq!(range.0, integer(25));
        assert_eq!(range.1, integer(41));
        assert_eq!(
            integral_span(&range.0, &range.1),
            IntegralPhaseCell::Levels {
                first: BigInt::from(25),
                last: BigInt::from(41),
            }
        );
    }
}
