//! Exact first-person reception of continuous caused geometry.
//!
//! A receiver is inside the construction.  It transports caused geometry
//! into its own frame and projects complete projective primitives onto its
//! local face.  The result is a continuous arrangement: no resolution,
//! address, pixel, sample count, or display lattice participates here.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use num_traits::{One, Signed, Zero};
use relational_geometry::{
    AffineMap3, Construction, EntityId, FrameId, FrameRelation, Geometry, GeometryEntity,
    LocalFrame, ProjectionError, ProjectionLaw, Rat, RatMat3, RatVec3, Receiver, ReceiverId,
    ReceiverOrientation, RelationId, TransportError,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ConicCellId, ConicClass, ConicError, ConicLineRelation, ConicRoot, CpuExecutionError,
    CpuExecutionReceipt, CpuExecutor, Edge, EventId, ExactOrdering, ExactTorus, ExactValue, FaceId,
    HingeId, HomogeneousConic, ImplicitCellId, ImplicitError, NativeConicPopulation, TorusRayFiber,
    VertexId, VertexLinkClass, canonical_homogeneous,
};

/// The intrinsic source population admitted to one receiver's local star.
///
/// This is not a visibility mask. It is the exact causal section which may
/// lawfully reach the receiver before projection. Exterior carriers can be
/// added by the caller only after an actual overlap/transport relation has
/// made them present.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverSourceSelection {
    pub entities: BTreeSet<EntityId>,
    pub conics: BTreeSet<ConicCellId>,
}

/// Exact source material underlying one receiver face before receiver motion
/// or projection. Comparing this section distinguishes deformation of the
/// construction from transport of an unchanged construction past a receiver.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverSourceSection {
    /// Exact chart population and frame transport carried by the source cut.
    ///
    /// This is presently conservative: all contemporary frame relations are
    /// retained so a changed transport path cannot masquerade as recurrence
    /// of unchanged local geometry.
    pub frames: BTreeMap<FrameId, LocalFrame>,
    pub frame_relations: BTreeMap<RelationId, FrameRelation>,
    pub entities: BTreeMap<EntityId, GeometryEntity>,
    pub conics: BTreeMap<ConicCellId, crate::NativeConic>,
    /// Receiver-local implicit bodies supplied at this exact source cut.
    ///
    /// These are not projected surrogates. Their native equations remain in
    /// the section so a first-person ray can be restricted against them.
    #[serde(default)]
    pub implicit_tori: BTreeMap<ImplicitCellId, ExactTorus>,
}

/// A proved co-transport between two differently inscribed source sections.
///
/// The map is not inferred from visual similarity. The two receiver ray
/// families determine one exact affine candidate, and every admitted source
/// constituent must verify against it. `hand` records whether the re-base
/// preserves or reverses the local orientation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverSourceRebase {
    pub map: AffineMap3,
    pub hand: i8,
}

/// How the receiver engine formed one exact local face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverFaceFormationCause {
    Projected,
    Retained {
        predecessor_event: EventId,
    },
    Rebased {
        predecessor_event: EventId,
        proof: Box<ReceiverSourceRebase>,
    },
}

/// Engine-owned factorization testimony. Its fields are crate-visible so an
/// application can carry and inspect the receipt but cannot mint a different
/// face and claim that the receiver transition formed it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFaceFormationReceipt {
    pub(crate) event: EventId,
    pub(crate) receiver: ReceiverId,
    pub(crate) source_section: ReceiverSourceSection,
    pub(crate) rays: RayFamily,
    pub(crate) orientation: ReceiverOrientation,
    pub(crate) face: ReceiverFace,
    pub(crate) cause: ReceiverFaceFormationCause,
}

impl ReceiverFaceFormationReceipt {
    pub fn event(&self) -> EventId {
        self.event
    }

    pub fn receiver(&self) -> ReceiverId {
        self.receiver
    }

    pub fn face(&self) -> &ReceiverFace {
        &self.face
    }

    pub fn source_section(&self) -> &ReceiverSourceSection {
        &self.source_section
    }

    pub fn rays(&self) -> &RayFamily {
        &self.rays
    }

    pub fn orientation(&self) -> &ReceiverOrientation {
        &self.orientation
    }

    pub fn cause(&self) -> &ReceiverFaceFormationCause {
        &self.cause
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertifiedReceiverFace {
    pub face: ReceiverFace,
    pub formation: ReceiverFaceFormationReceipt,
}

impl ReceiverSourceSection {
    /// Prove that `target` is this exact source section carried through the
    /// same affine map which carries `source_rays` into `target_rays`.
    ///
    /// This is deliberately strict. Frame incidence, entity identity, conic
    /// law, and source chronology must remain exact. Only their geometric
    /// inscription may move. A receiver-local implicit body currently forces
    /// fresh factorization because no exact affine carrier for its native
    /// quartic species has yet been declared.
    pub fn exact_rebase_to(
        &self,
        target: &Self,
        source_rays: &RayFamily,
        target_rays: &RayFamily,
    ) -> Option<ReceiverSourceRebase> {
        let map = source_rays.exact_affine_rebase_to(target_rays)?;
        if self.frames != target.frames
            || self.frame_relations != target.frame_relations
            || self.entities.keys().ne(target.entities.keys())
            || self.conics.keys().ne(target.conics.keys())
            || !self.implicit_tori.is_empty()
            || !target.implicit_tori.is_empty()
        {
            return None;
        }
        if !self.entities.iter().all(|(id, source)| {
            target
                .entities
                .get(id)
                .is_some_and(|target| entity_rebases(source, target, &map))
        }) {
            return None;
        }
        if !self.conics.iter().all(|(id, source)| {
            target
                .conics
                .get(id)
                .is_some_and(|target| native_conic_rebases(source, target, &map))
        }) {
            return None;
        }
        let determinant = map.linear.determinant();
        Some(ReceiverSourceRebase {
            hand: if determinant.is_positive() { 1 } else { -1 },
            map,
        })
    }
}

fn entity_rebases(source: &GeometryEntity, target: &GeometryEntity, map: &AffineMap3) -> bool {
    source.id == target.id
        && source.name == target.name
        && source.frame == target.frame
        && geometry_rebases(&source.geometry, &target.geometry, map)
}

fn geometry_rebases(source: &Geometry, target: &Geometry, map: &AffineMap3) -> bool {
    match (source, target) {
        (
            Geometry::Triangle {
                vertices: source_vertices,
            },
            Geometry::Triangle {
                vertices: target_vertices,
            },
        ) => source_vertices
            .iter()
            .zip(target_vertices)
            .all(|(source, target)| map.apply(source) == *target),
        (
            Geometry::Thread {
                vertices: source_vertices,
                closed: source_closed,
            },
            Geometry::Thread {
                vertices: target_vertices,
                closed: target_closed,
            },
        ) => {
            source_closed == target_closed
                && source_vertices.len() == target_vertices.len()
                && source_vertices
                    .iter()
                    .zip(target_vertices)
                    .all(|(source, target)| map.apply(source) == *target)
        }
        (Geometry::Conic(source), Geometry::Conic(target)) => {
            source.species == target.species
                && map.apply(&source.center) == target.center
                && map.linear.apply(&source.axis_u) == target.axis_u
                && map.linear.apply(&source.axis_v) == target.axis_v
        }
        _ => false,
    }
}

fn native_conic_rebases(
    source: &crate::NativeConic,
    target: &crate::NativeConic,
    map: &AffineMap3,
) -> bool {
    source.id == target.id
        && source.name == target.name
        && source.source_event == target.source_event
        && source.last_event == target.last_event
        && source.frame == target.frame
        && source.form == target.form
        && map.apply(&source.chart.origin) == target.chart.origin
        && map.linear.apply(&source.chart.axis_x) == target.chart.axis_x
        && map.linear.apply(&source.chart.axis_y) == target.chart.axis_y
}

impl ReceiverSourceSelection {
    pub fn section(
        &self,
        construction: &Construction,
        conics: &NativeConicPopulation,
    ) -> Result<ReceiverSourceSection, ReceiverError> {
        let entities = self
            .entities
            .iter()
            .map(|entity| {
                construction
                    .entities
                    .get(entity)
                    .cloned()
                    .map(|body| (*entity, body))
                    .ok_or(ReceiverError::MissingSelectedEntity(*entity))
            })
            .collect::<Result<_, _>>()?;
        let conics = self
            .conics
            .iter()
            .map(|conic| {
                conics
                    .cells
                    .get(conic)
                    .cloned()
                    .map(|body| (*conic, body))
                    .ok_or(ReceiverError::MissingSelectedConic(*conic))
            })
            .collect::<Result<_, _>>()?;
        Ok(ReceiverSourceSection {
            frames: construction.frames.clone(),
            frame_relations: construction.relations.clone(),
            entities,
            conics,
            implicit_tori: BTreeMap::new(),
        })
    }
}

/// Continuous exact extent of one receiver's local affine chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFaceExtent {
    pub horizontal_span: Rat,
    pub vertical_span: Rat,
}

impl ReceiverFaceExtent {
    pub fn validate(&self) -> Result<(), ReceiverError> {
        if !self.horizontal_span.is_positive() || !self.vertical_span.is_positive() {
            return Err(ReceiverError::InvalidFaceExtent);
        }
        Ok(())
    }

    pub fn bounds(&self) -> [[Rat; 2]; 2] {
        let two = Rat::from_integer(2.into());
        let horizontal_half = &self.horizontal_span / &two;
        let vertical_half = &self.vertical_span / two;
        [
            [-horizontal_half.clone(), -vertical_half.clone()],
            [horizontal_half, vertical_half],
        ]
    }

    pub fn contains(&self, coordinate: &[Rat; 2]) -> bool {
        let [lower, upper] = self.bounds();
        coordinate[0] >= lower[0]
            && coordinate[0] <= upper[0]
            && coordinate[1] >= lower[1]
            && coordinate[1] <= upper[1]
    }
}

/// One actual directional organ in a receiver's contemporary simplicial
/// horizon.
///
/// The organ is the cone from the receiver anchor over one oriented link
/// cell. Its two boundary directions, central direction, and oriented area
/// are exact relative vectors. No angular sample or screen address appears in
/// this carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAcceptanceOrgan {
    pub face: FaceId,
    pub link_edge: Edge,
    pub from: VertexId,
    pub to: VertexId,
    pub hand: i8,
    pub boundary_directions: [RatVec3; 2],
    pub central_direction: RatVec3,
    pub oriented_area: RatVec3,
}

/// Incidence through which neighboring directional organs overlap.
///
/// Regular cycles have one incoming and one outgoing organ at every seam.
/// Paths expose endpoints, while a singular link retains the full plural
/// population instead of being coerced into a cyclic order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAcceptanceSeam {
    pub vertex: VertexId,
    pub direction: RatVec3,
    pub incoming: Vec<FaceId>,
    pub outgoing: Vec<FaceId>,
}

/// The source-declared port section used when a single finite projective chart
/// is requested from a plural directional cover.
///
/// `forward` is the actual anchor-to-port direction. `negative_face` and
/// `positive_face` are selected by the two oriented coface hands, so the
/// transverse basis is not selected by map order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPortSection {
    pub port: HingeId,
    pub distal: VertexId,
    pub negative_face: FaceId,
    pub positive_face: FaceId,
    pub forward: RatVec3,
    pub horizontal: RatVec3,
    pub vertical: RatVec3,
}

/// Complete finite directional cover owned by one receiver occurrence.
///
/// A terminal face is one declared port chart of this cover. The cover
/// remains standing so the other organs, their seams, and their cyclic or
/// singular organization are not erased by that observation choice.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAcceptanceCover {
    pub event: EventId,
    pub receiver: ReceiverId,
    pub anchor: VertexId,
    pub link_class: VertexLinkClass,
    pub organs: Vec<ReceiverAcceptanceOrgan>,
    pub seams: Vec<ReceiverAcceptanceSeam>,
    pub port_section: ReceiverPortSection,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFaceSpec {
    pub receiver: Receiver,
    pub extent: ReceiverFaceExtent,
    pub rays: RayFamily,
    /// The complete directional horizon which caused this particular port
    /// chart. Generic geometric receivers may omit it; local-star receivers
    /// must derive it from contemporary standing.
    pub acceptance: Option<ReceiverAcceptanceCover>,
}

/// The receiver's exact local ray law.  Neither species requires normalized
/// vectors: incidence and projective projection are scale invariant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RayFamily {
    Parallel {
        face_center: RatVec3,
        horizontal: RatVec3,
        vertical: RatVec3,
        direction: RatVec3,
    },
    Central {
        center: RatVec3,
        forward: RatVec3,
        horizontal: RatVec3,
        vertical: RatVec3,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactRay {
    pub origin: RatVec3,
    pub direction: RatVec3,
}

/// Homogeneous point `[x:y:w]` on a receiver face.  Points at infinity remain
/// legitimate members and are never coerced into an affine decimal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectivePoint2 {
    pub x: Rat,
    pub y: Rat,
    pub w: Rat,
}

impl ProjectivePoint2 {
    pub fn new(x: Rat, y: Rat, w: Rat) -> Result<Self, ReceiverError> {
        if x.is_zero() && y.is_zero() && w.is_zero() {
            return Err(ReceiverError::ZeroProjectivePoint);
        }
        Ok(Self { x, y, w })
    }

    pub fn affine(&self) -> Option<[Rat; 2]> {
        (!self.w.is_zero()).then(|| [&self.x / &self.w, &self.y / &self.w])
    }

    pub fn cross(&self, other: &Self) -> ProjectiveLine2 {
        ProjectiveLine2::homogeneous(
            &self.y * &other.w - &self.w * &other.y,
            &self.w * &other.x - &self.x * &other.w,
            &self.x * &other.y - &self.y * &other.x,
        )
    }
}

/// Homogeneous line `a*x+b*y+c*w=0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveLine2 {
    pub a: Rat,
    pub b: Rat,
    pub c: Rat,
}

impl ProjectiveLine2 {
    /// Construct one geometric line from its homogeneous coefficients.
    ///
    /// This constructor is for independently meaningful lines. A coefficient
    /// in a parameterized line family must retain its relative scale and must
    /// not be normalized independently from that family.
    pub fn homogeneous(a: Rat, b: Rat, c: Rat) -> Self {
        let [a, b, c] = canonical_homogeneous([a, b, c]);
        Self { a, b, c }
    }

    pub fn cross(&self, other: &Self) -> Option<ProjectivePoint2> {
        ProjectivePoint2::new(
            &self.b * &other.c - &self.c * &other.b,
            &self.c * &other.a - &self.a * &other.c,
            &self.a * &other.b - &self.b * &other.a,
        )
        .ok()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ReceiverPrimitiveId {
    Entity(EntityId),
    NativeConic(ConicCellId),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedTriangle {
    pub source: ReceiverPrimitiveId,
    pub vertices: [ProjectivePoint2; 3],
    pub receiver_depths: [Rat; 3],
    pub receiver_depth: Option<Box<ProjectiveDepthLaw>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedThread {
    pub source: ReceiverPrimitiveId,
    pub vertices: Vec<ProjectivePoint2>,
    pub receiver_depths: Vec<Rat>,
    pub closed: bool,
}

/// Exact receiver-ray depth as a ratio of two homogeneous linear forms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveDepthLaw {
    pub numerator: ProjectiveLine2,
    pub denominator: ProjectiveLine2,
}

impl ProjectiveDepthLaw {
    pub fn evaluate(&self, point: &ProjectivePoint2) -> Option<Rat> {
        let evaluate =
            |line: &ProjectiveLine2| &line.a * &point.x + &line.b * &point.y + &line.c * &point.w;
        let denominator = evaluate(&self.denominator);
        (!denominator.is_zero()).then(|| evaluate(&self.numerator) / denominator)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedConic {
    pub source: ReceiverPrimitiveId,
    pub form: HomogeneousConic,
    pub class_in_receiver_chart: ConicClass,
    pub receiver_depth: ProjectiveDepthLaw,
}

/// One exact family `L(t)=L_0+t L_1` of transported local coordinate lines.
/// It is a continuous foliation, not a radius-bounded collection of samples.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveLineFamily {
    pub zero: ProjectiveLine2,
    pub coefficient: ProjectiveLine2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportedCoordinateField {
    pub source_frame: FrameId,
    pub first_axis: ProjectiveLineFamily,
    pub second_axis: ProjectiveLineFamily,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverPrimitive {
    Triangle(ProjectedTriangle),
    Conic(ProjectedConic),
    Thread(ProjectedThread),
}

impl ReceiverPrimitive {
    pub fn id(&self) -> ReceiverPrimitiveId {
        match self {
            Self::Triangle(triangle) => triangle.source,
            Self::Conic(conic) => conic.source,
            Self::Thread(thread) => thread.source,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinearPiece {
    pub primitive: ReceiverPrimitiveId,
    pub ordinal: usize,
    pub start: ProjectivePoint2,
    pub end: ProjectivePoint2,
    pub support: ProjectiveLine2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactSegmentMembership {
    Interior,
    Boundary,
    Outside,
    Open,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArrangementRelation {
    LinearCrossing {
        left: Box<LinearPiece>,
        right: Box<LinearPiece>,
        point: ProjectivePoint2,
        left_membership: ExactSegmentMembership,
        right_membership: ExactSegmentMembership,
    },
    LinearConicCrossing {
        linear: Box<LinearPiece>,
        conic: ReceiverPrimitiveId,
        parameter: ExactValue,
        multiplicity: u32,
        hand: i8,
        membership: ExactSegmentMembership,
    },
    CoincidentLinearConic {
        linear: Box<LinearPiece>,
        conic: ReceiverPrimitiveId,
    },
    /// The two exact implicit quadratics are the complete intersection
    /// relation.  No preferred elimination axis or approximate root list is
    /// installed into their identity.
    ConicConicPencil {
        left: ReceiverPrimitiveId,
        right: ReceiverPrimitiveId,
        left_form: Box<HomogeneousConic>,
        right_form: Box<HomogeneousConic>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArrangementSeam {
    ProjectionCollapsed {
        source: ReceiverPrimitiveId,
    },
    /// A source member occupies the receiver's contemporary center.  The
    /// member is a physical/projective contact, not a point which can be
    /// divided into `[0:0:0]`.  The contacted primitive remains open at this
    /// face instead of aborting the complete receiver event.
    ReceiverPointContact {
        source: ReceiverPrimitiveId,
        ordinal: usize,
    },
    PointAtInfinityInSegmentTest {
        primitive: ReceiverPrimitiveId,
        ordinal: usize,
    },
    CoordinateFieldCollapsed {
        frame: FrameId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverArrangement {
    pub primitives: Vec<ReceiverPrimitive>,
    pub coordinate_fields: Vec<TransportedCoordinateField>,
    pub linear_pieces: Vec<LinearPiece>,
    pub relations: Vec<ArrangementRelation>,
    pub seams: Vec<ArrangementSeam>,
}

/// One complete contemporary receiver face before any finite presentation
/// quotient or receiver-to-receiver assembly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFace {
    pub schema: String,
    pub receiver: ReceiverId,
    pub extent: ReceiverFaceExtent,
    pub rays: RayFamily,
    pub acceptance: Option<ReceiverAcceptanceCover>,
    pub arrangement: ReceiverArrangement,
    /// Native receiver-local quartic supports. They retain their 3D implicit
    /// laws because a 2D conic surrogate would erase their multivalued depth.
    pub implicit_tori: Vec<ExactTorus>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SurfaceCrossing {
    pub entity: EntityId,
    pub ray_parameter: Rat,
    pub barycentric: [Rat; 3],
    pub orientation: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CurveCrossingKind {
    Thread { segment: usize, parameter: Rat },
    Conic,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurveCrossing {
    pub primitive: ReceiverPrimitiveId,
    pub ray_parameter: Rat,
    pub kind: CurveCrossingKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossingLayer {
    pub ray_parameter: Rat,
    pub crossings: Vec<SurfaceCrossing>,
    pub curve_crossings: Vec<CurveCrossing>,
}

/// A direct first-person query of the already-formed continuous face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaceFiber {
    pub face_coordinate: [Rat; 2],
    pub ray: ExactRay,
    pub layers: Vec<CrossingLayer>,
    pub implicit_fibers: Vec<TorusRayFiber>,
}

/// Exact support testimony for a receiver direction which lies on the
/// projective horizon of the selected finite chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverHorizonContact {
    Linear {
        primitive: ReceiverPrimitiveId,
        ordinal: usize,
    },
    Conic {
        primitive: ReceiverPrimitiveId,
    },
}

/// One exact direction/depth fiber of a receiver's plural acceptance cover.
///
/// A direction outside the finite affine port chart does not disappear. It
/// remains a projective-horizon fiber with its exact support contacts and
/// native implicit roots.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverProjectiveHorizonFiber {
    pub direction: RatVec3,
    pub coordinate: ProjectivePoint2,
    pub ray: ExactRay,
    pub contacts: Vec<ReceiverHorizonContact>,
    pub implicit_fibers: Vec<TorusRayFiber>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverDirectionalFiber {
    Finite(Box<FaceFiber>),
    /// The caused organ or seam collapses at the receiver center and therefore
    /// has no projective ray. It remains explicit instead of aborting the
    /// other directional sections.
    SingularDirection {
        direction: RatVec3,
    },
    ProjectiveHorizon(Box<ReceiverProjectiveHorizonFiber>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverOrganSection {
    pub face: FaceId,
    pub fiber: ReceiverDirectionalFiber,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverSeamSection {
    pub vertex: VertexId,
    pub fiber: ReceiverDirectionalFiber,
}

/// The complete center-direction section computed from an already-formed
/// receiver face and its contemporary oriented link cover.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAcceptanceSection {
    pub event: EventId,
    pub receiver: ReceiverId,
    pub organs: Vec<ReceiverOrganSection>,
    pub seams: Vec<ReceiverSeamSection>,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverError {
    #[error("receiver face spans must be positive")]
    InvalidFaceExtent,
    #[error("receiver ray family contains a collapsed projective basis")]
    DegenerateRayFamily,
    #[error("receiver {0:?}'s declared projection species conflicts with its exact ray family")]
    ProjectionSpeciesMismatch(ReceiverId),
    #[error("the zero homogeneous triple is not a projective point")]
    ZeroProjectivePoint,
    #[error("the requested coordinate lies outside receiver {0:?}'s local face")]
    CoordinateOutsideFace(ReceiverId),
    #[error("a projected conic homography collapsed")]
    CollapsedConicProjection,
    #[error("one parallel receiver-face worker failed before returning its complete face")]
    WorkerPanicked,
    #[error("receiver source selections do not match the requested receiver population")]
    SourceSelectionPopulationMismatch,
    #[error("receiver implicit-source sections do not match the requested receiver population")]
    ImplicitSourcePopulationMismatch,
    #[error(
        "receiver {receiver:?}'s implicit-source key {key:?} does not match body identity {body:?}"
    )]
    ImplicitSourceIdentityMismatch {
        receiver: ReceiverId,
        key: ImplicitCellId,
        body: ImplicitCellId,
    },
    #[error(
        "receiver {receiver:?}'s implicit body {body:?} begins at {source_event:?} after its last event {last_event:?}"
    )]
    ImplicitSourceChronologyInverted {
        receiver: ReceiverId,
        body: ImplicitCellId,
        source_event: EventId,
        last_event: EventId,
    },
    #[error(
        "receiver {receiver:?}'s implicit body {body:?} at {last_event:?} is later than face formation {formation_event:?}"
    )]
    ImplicitSourceAfterFormation {
        receiver: ReceiverId,
        body: ImplicitCellId,
        last_event: EventId,
        formation_event: EventId,
    },
    #[error("receiver {0:?}'s formed face has no directional acceptance cover")]
    MissingAcceptanceCover(ReceiverId),
    #[error("selected source entity {0:?} is absent from the contemporary construction")]
    MissingSelectedEntity(EntityId),
    #[error("selected native conic {0:?} is absent from the contemporary construction")]
    MissingSelectedConic(ConicCellId),
    #[error(transparent)]
    Implicit(#[from] ImplicitError),
    #[error(transparent)]
    Transport(#[from] TransportError),
    #[error(transparent)]
    Projection(#[from] ProjectionError),
    #[error(transparent)]
    Conic(#[from] ConicError),
}

impl RayFamily {
    pub fn validate(&self) -> Result<(), ReceiverError> {
        let basis = self.projective_basis();
        if basis.determinant().is_zero() {
            return Err(ReceiverError::DegenerateRayFamily);
        }
        Ok(())
    }

    fn projective_basis(&self) -> RatMat3 {
        let (horizontal, vertical, depth) = match self {
            Self::Parallel {
                horizontal,
                vertical,
                direction,
                ..
            } => (horizontal, vertical, direction),
            Self::Central {
                horizontal,
                vertical,
                forward,
                ..
            } => (horizontal, vertical, forward),
        };
        matrix_from_columns(horizontal, vertical, depth)
    }

    /// Derive the unique affine map which co-transports this complete ray
    /// basis into `target`. Opposed ray species do not silently coerce.
    pub fn exact_affine_rebase_to(&self, target: &Self) -> Option<AffineMap3> {
        let (source_center, target_center) = match (self, target) {
            (
                Self::Parallel {
                    face_center: source,
                    ..
                },
                Self::Parallel {
                    face_center: target,
                    ..
                },
            )
            | (Self::Central { center: source, .. }, Self::Central { center: target, .. }) => {
                (source, target)
            }
            _ => return None,
        };
        let source_inverse = self.projective_basis().inverse()?;
        let linear = target.projective_basis().multiply(&source_inverse);
        let translation = target_center.subtract(&linear.apply(source_center));
        Some(AffineMap3 {
            linear,
            translation,
        })
    }

    pub fn ray(&self, coordinate: &[Rat; 2]) -> ExactRay {
        match self {
            Self::Parallel {
                face_center,
                horizontal,
                vertical,
                direction,
            } => ExactRay {
                origin: face_center
                    .add(&horizontal.scale(&coordinate[0]))
                    .add(&vertical.scale(&coordinate[1])),
                direction: direction.clone(),
            },
            Self::Central {
                center,
                forward,
                horizontal,
                vertical,
            } => ExactRay {
                origin: center.clone(),
                direction: forward
                    .add(&horizontal.scale(&coordinate[0]))
                    .add(&vertical.scale(&coordinate[1])),
            },
        }
    }

    pub fn project_point(&self, point: &RatVec3) -> Result<ProjectivePoint2, ReceiverError> {
        let local = self.project_coefficients_point(point)?;
        match self {
            Self::Parallel { .. } => ProjectivePoint2::new(local.x, local.y, Rat::one()),
            Self::Central { .. } => ProjectivePoint2::new(local.x, local.y, local.z),
        }
    }

    pub fn project_depth(&self, point: &RatVec3) -> Result<Rat, ReceiverError> {
        Ok(self.project_coefficients_point(point)?.z)
    }

    pub fn project_direction(
        &self,
        direction: &RatVec3,
    ) -> Result<ProjectivePoint2, ReceiverError> {
        let local = self.project_coefficients_direction(direction)?;
        match self {
            Self::Parallel { .. } => ProjectivePoint2::new(local.x, local.y, Rat::zero()),
            Self::Central { .. } => ProjectivePoint2::new(local.x, local.y, local.z),
        }
    }

    fn project_coefficients_point(&self, point: &RatVec3) -> Result<RatVec3, ReceiverError> {
        let inverse = self
            .projective_basis()
            .inverse()
            .ok_or(ReceiverError::DegenerateRayFamily)?;
        match self {
            Self::Parallel { face_center, .. } => Ok(inverse.apply(&point.subtract(face_center))),
            Self::Central { center, .. } => Ok(inverse.apply(&point.subtract(center))),
        }
    }

    fn project_coefficients_direction(
        &self,
        direction: &RatVec3,
    ) -> Result<RatVec3, ReceiverError> {
        self.projective_basis()
            .inverse()
            .map(|inverse| inverse.apply(direction))
            .ok_or(ReceiverError::DegenerateRayFamily)
    }
}

fn matrix_from_columns(first: &RatVec3, second: &RatVec3, third: &RatVec3) -> RatMat3 {
    RatMat3::new([
        [first.x.clone(), second.x.clone(), third.x.clone()],
        [first.y.clone(), second.y.clone(), third.y.clone()],
        [first.z.clone(), second.z.clone(), third.z.clone()],
    ])
}

fn projective_matrix_from_columns(
    first: &ProjectivePoint2,
    second: &ProjectivePoint2,
    third: &ProjectivePoint2,
) -> RatMat3 {
    RatMat3::new([
        [first.x.clone(), second.x.clone(), third.x.clone()],
        [first.y.clone(), second.y.clone(), third.y.clone()],
        [first.w.clone(), second.w.clone(), third.w.clone()],
    ])
}

fn project_conic(
    source: ReceiverPrimitiveId,
    chart_origin: &RatVec3,
    chart_x: &RatVec3,
    chart_y: &RatVec3,
    form: &HomogeneousConic,
    rays: &RayFamily,
) -> Result<ProjectedConic, ReceiverError> {
    let first_coefficients = rays.project_coefficients_direction(chart_x)?;
    let second_coefficients = rays.project_coefficients_direction(chart_y)?;
    let origin_coefficients = rays.project_coefficients_point(chart_origin)?;
    let map = match rays {
        RayFamily::Parallel { .. } => RatMat3::new([
            [
                first_coefficients.x.clone(),
                second_coefficients.x.clone(),
                origin_coefficients.x.clone(),
            ],
            [
                first_coefficients.y.clone(),
                second_coefficients.y.clone(),
                origin_coefficients.y.clone(),
            ],
            [Rat::zero(), Rat::zero(), Rat::one()],
        ]),
        RayFamily::Central { .. } => matrix_from_columns(
            &first_coefficients,
            &second_coefficients,
            &origin_coefficients,
        ),
    };
    let inverse = map
        .inverse()
        .ok_or(ReceiverError::CollapsedConicProjection)?;
    let transported = inverse
        .transpose()
        .multiply(&form.doubled_matrix())
        .multiply(&inverse);
    let form = HomogeneousConic::from_doubled_matrix(&transported)?;
    Ok(ProjectedConic {
        source,
        class_in_receiver_chart: form.classify(),
        form,
        receiver_depth: ProjectiveDepthLaw {
            numerator: row_times_matrix(
                [
                    first_coefficients.z,
                    second_coefficients.z,
                    origin_coefficients.z,
                ],
                &inverse,
            ),
            denominator: row_times_matrix([Rat::zero(), Rat::zero(), Rat::one()], &inverse),
        },
    })
}

fn row_times_matrix(row: [Rat; 3], matrix: &RatMat3) -> ProjectiveLine2 {
    let entry = |column: usize| {
        &row[0] * &matrix.rows[0][column]
            + &row[1] * &matrix.rows[1][column]
            + &row[2] * &matrix.rows[2][column]
    };
    ProjectiveLine2 {
        a: entry(0),
        b: entry(1),
        c: entry(2),
    }
}

fn transported_point(
    construction: &Construction,
    receiver: &Receiver,
    source: FrameId,
    point: &RatVec3,
) -> Result<RatVec3, ReceiverError> {
    let transport = if let Some(route) = receiver.route_overrides.get(&source) {
        construction.transport_via(source, receiver.frame, route)?
    } else {
        construction.transport(source, receiver.frame)?
    };
    Ok(receiver.orientation.matrix().apply(&transport.apply(point)))
}

fn transported_direction(
    construction: &Construction,
    receiver: &Receiver,
    source: FrameId,
    direction: &RatVec3,
) -> Result<RatVec3, ReceiverError> {
    let transport = if let Some(route) = receiver.route_overrides.get(&source) {
        construction.transport_via(source, receiver.frame, route)?
    } else {
        construction.transport(source, receiver.frame)?
    };
    Ok(receiver
        .orientation
        .matrix()
        .apply(&transport.linear.apply(direction)))
}

fn triangle_depth_law(
    rays: &RayFamily,
    vertices: &[ProjectivePoint2; 3],
    depths: &[Rat; 3],
) -> Option<ProjectiveDepthLaw> {
    let affine = vertices
        .iter()
        .map(ProjectivePoint2::affine)
        .collect::<Option<Vec<_>>>()?;
    let interpolation = RatMat3::new([
        [affine[0][0].clone(), affine[0][1].clone(), Rat::one()],
        [affine[1][0].clone(), affine[1][1].clone(), Rat::one()],
        [affine[2][0].clone(), affine[2][1].clone(), Rat::one()],
    ])
    .inverse()?;
    let coefficients = |values: [Rat; 3]| {
        let result = interpolation.apply(&RatVec3::new(
            values[0].clone(),
            values[1].clone(),
            values[2].clone(),
        ));
        ProjectiveLine2 {
            a: result.x,
            b: result.y,
            c: result.z,
        }
    };
    match rays {
        RayFamily::Parallel { .. } => Some(ProjectiveDepthLaw {
            numerator: coefficients(depths.clone()),
            denominator: ProjectiveLine2 {
                a: Rat::zero(),
                b: Rat::zero(),
                c: Rat::one(),
            },
        }),
        RayFamily::Central { .. } => {
            if depths.iter().any(Rat::is_zero) {
                return None;
            }
            Some(ProjectiveDepthLaw {
                numerator: ProjectiveLine2 {
                    a: Rat::zero(),
                    b: Rat::zero(),
                    c: Rat::one(),
                },
                denominator: coefficients(depths.clone().map(|depth| Rat::one() / depth)),
            })
        }
    }
}

pub fn receive_face(
    construction: &Construction,
    specification: &ReceiverFaceSpec,
) -> Result<ReceiverFace, ReceiverError> {
    receive_face_selected(
        construction,
        None,
        specification,
        None,
        None,
        true,
        &crate::CpuExecutor::serial(),
    )
}

pub fn receive_face_entities(
    construction: &Construction,
    specification: &ReceiverFaceSpec,
    admitted_entities: &BTreeSet<EntityId>,
) -> Result<ReceiverFace, ReceiverError> {
    receive_face_selected(
        construction,
        None,
        specification,
        Some(admitted_entities),
        None,
        true,
        &crate::CpuExecutor::serial(),
    )
}

pub fn receive_face_with_conics(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specification: &ReceiverFaceSpec,
) -> Result<ReceiverFace, ReceiverError> {
    receive_face_selected(
        construction,
        Some(conics),
        specification,
        None,
        None,
        true,
        &crate::CpuExecutor::serial(),
    )
}

/// Receive a co-present population of complete faces in parallel. Physical
/// scheduling cannot become receiver chronology: results return in the
/// supplied receiver order through the canonical indexed executor.
pub fn receive_faces_with_conics_cpu(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specifications: &[ReceiverFaceSpec],
    executor: &CpuExecutor,
) -> Result<(Vec<ReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    executor
        .execute_indexed(specifications, |_index, specification| {
            receive_face_selected(
                construction,
                Some(conics),
                specification,
                None,
                None,
                true,
                executor,
            )
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => ReceiverError::WorkerPanicked,
        })
}

/// Receive the same complete continuous primitives and transported coordinate
/// fields without deriving the separate all-crossings atlas. This is the
/// lawful live support face for observers whose next deed depends on support,
/// not on possession of every pairwise proof witness.
pub fn receive_support_faces_with_conics_cpu(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specifications: &[ReceiverFaceSpec],
    executor: &CpuExecutor,
) -> Result<(Vec<ReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    executor
        .execute_indexed(specifications, |_index, specification| {
            receive_face_selected(
                construction,
                Some(conics),
                specification,
                None,
                None,
                false,
                executor,
            )
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => ReceiverError::WorkerPanicked,
        })
}

/// Receive one exact star-local source section per receiver without deriving
/// the separate all-crossings atlas.
///
/// Unlike `receive_support_faces_with_conics_cpu`, this entry point never
/// multiplies the complete construction through every receiver. The caller
/// must supply one explicit intrinsic/exterior source cut for every requested
/// receiver.
pub fn receive_selected_support_faces_with_conics_cpu(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specifications: &[ReceiverFaceSpec],
    selections: &BTreeMap<ReceiverId, ReceiverSourceSelection>,
    executor: &CpuExecutor,
) -> Result<(Vec<ReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    receive_selected_faces_with_conics_cpu_inner(
        construction,
        conics,
        specifications,
        selections,
        false,
        executor,
    )
}

/// Receive one exact star-local source section per receiver and form crossing
/// relations only inside each selected section.
///
/// This is the sparse topology-bearing counterpart of the support-only
/// entry point. It never forms the Cartesian product of the complete
/// construction with the receiver population.
pub fn receive_selected_faces_with_conics_cpu(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specifications: &[ReceiverFaceSpec],
    selections: &BTreeMap<ReceiverId, ReceiverSourceSelection>,
    executor: &CpuExecutor,
) -> Result<(Vec<ReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    receive_selected_faces_with_conics_cpu_inner(
        construction,
        conics,
        specifications,
        selections,
        true,
        executor,
    )
}

/// Form selected receiver faces together with unforgeable-in-API
/// factorization testimony for an exact physical occurrence.
pub fn receive_selected_faces_with_conics_certified_cpu(
    event: EventId,
    construction: &Construction,
    conics: &NativeConicPopulation,
    specifications: &[ReceiverFaceSpec],
    selections: &BTreeMap<ReceiverId, ReceiverSourceSelection>,
    executor: &CpuExecutor,
) -> Result<(Vec<CertifiedReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    let implicit_tori = specifications
        .iter()
        .map(|specification| (specification.receiver.id, BTreeMap::new()))
        .collect();
    receive_selected_faces_with_implicit_tori_certified_cpu(
        event,
        construction,
        conics,
        &implicit_tori,
        specifications,
        selections,
        executor,
    )
}

/// Form certified receiver faces with exact receiver-local implicit bodies.
///
/// The implicit population is source material, not a post-formation
/// decoration. It must name exactly the requested receivers; each map key
/// must equal the native body's identity; and its complete chronology must
/// precede this formation occurrence.
#[allow(clippy::too_many_arguments)]
pub fn receive_selected_faces_with_implicit_tori_certified_cpu(
    event: EventId,
    construction: &Construction,
    conics: &NativeConicPopulation,
    implicit_tori: &BTreeMap<ReceiverId, BTreeMap<ImplicitCellId, ExactTorus>>,
    specifications: &[ReceiverFaceSpec],
    selections: &BTreeMap<ReceiverId, ReceiverSourceSelection>,
    executor: &CpuExecutor,
) -> Result<(Vec<CertifiedReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    validate_implicit_source_population(event, specifications, implicit_tori)?;
    let (faces, execution) = receive_selected_faces_with_conics_cpu(
        construction,
        conics,
        specifications,
        selections,
        executor,
    )?;
    let certified = specifications
        .iter()
        .zip(faces)
        .map(|(specification, mut face)| {
            let receiver = specification.receiver.id;
            let mut source_section = selections
                .get(&receiver)
                .expect("selection population was checked by face formation")
                .section(construction, conics)?;
            source_section.implicit_tori = implicit_tori
                .get(&receiver)
                .expect("implicit population was checked")
                .clone();
            face.implicit_tori = source_section.implicit_tori.values().cloned().collect();
            let formation = ReceiverFaceFormationReceipt {
                event,
                receiver,
                source_section,
                rays: specification.rays.clone(),
                orientation: specification.receiver.orientation.clone(),
                face: face.clone(),
                cause: ReceiverFaceFormationCause::Projected,
            };
            Ok(CertifiedReceiverFace { face, formation })
        })
        .collect::<Result<_, ReceiverError>>()?;
    Ok((certified, execution))
}

fn validate_implicit_source_population(
    event: EventId,
    specifications: &[ReceiverFaceSpec],
    implicit_tori: &BTreeMap<ReceiverId, BTreeMap<ImplicitCellId, ExactTorus>>,
) -> Result<(), ReceiverError> {
    let requested = specifications
        .iter()
        .map(|specification| specification.receiver.id)
        .collect::<BTreeSet<_>>();
    if requested != implicit_tori.keys().copied().collect::<BTreeSet<_>>() {
        return Err(ReceiverError::ImplicitSourcePopulationMismatch);
    }
    for (receiver, tori) in implicit_tori {
        for (key, torus) in tori {
            if *key != torus.id {
                return Err(ReceiverError::ImplicitSourceIdentityMismatch {
                    receiver: *receiver,
                    key: *key,
                    body: torus.id,
                });
            }
            if torus.source_event > torus.last_event {
                return Err(ReceiverError::ImplicitSourceChronologyInverted {
                    receiver: *receiver,
                    body: torus.id,
                    source_event: torus.source_event,
                    last_event: torus.last_event,
                });
            }
            if torus.last_event > event {
                return Err(ReceiverError::ImplicitSourceAfterFormation {
                    receiver: *receiver,
                    body: torus.id,
                    last_event: torus.last_event,
                    formation_event: event,
                });
            }
        }
    }
    Ok(())
}

fn receive_selected_faces_with_conics_cpu_inner(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specifications: &[ReceiverFaceSpec],
    selections: &BTreeMap<ReceiverId, ReceiverSourceSelection>,
    form_crossing_atlas: bool,
    executor: &CpuExecutor,
) -> Result<(Vec<ReceiverFace>, CpuExecutionReceipt), ReceiverError> {
    let requested = specifications
        .iter()
        .map(|specification| specification.receiver.id)
        .collect::<BTreeSet<_>>();
    if requested.len() != specifications.len()
        || requested != selections.keys().copied().collect::<BTreeSet<_>>()
    {
        return Err(ReceiverError::SourceSelectionPopulationMismatch);
    }
    executor
        .execute_indexed(specifications, |_index, specification| {
            let selection = selections
                .get(&specification.receiver.id)
                .expect("selection population was checked");
            receive_face_selected(
                construction,
                Some(conics),
                specification,
                Some(&selection.entities),
                Some(&selection.conics),
                form_crossing_atlas,
                executor,
            )
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => ReceiverError::WorkerPanicked,
        })
}

pub fn receive_face_with_selected_conics(
    construction: &Construction,
    conics: &NativeConicPopulation,
    specification: &ReceiverFaceSpec,
    admitted_entities: Option<&BTreeSet<EntityId>>,
    admitted_conics: Option<&BTreeSet<ConicCellId>>,
) -> Result<ReceiverFace, ReceiverError> {
    receive_face_selected(
        construction,
        Some(conics),
        specification,
        admitted_entities,
        admitted_conics,
        true,
        &crate::CpuExecutor::serial(),
    )
}

fn receive_face_selected(
    construction: &Construction,
    conics: Option<&NativeConicPopulation>,
    specification: &ReceiverFaceSpec,
    admitted_entities: Option<&BTreeSet<EntityId>>,
    admitted_conics: Option<&BTreeSet<ConicCellId>>,
    form_crossing_atlas: bool,
    executor: &CpuExecutor,
) -> Result<ReceiverFace, ReceiverError> {
    specification.extent.validate()?;
    specification.rays.validate()?;
    match (&specification.receiver.projection, &specification.rays) {
        (ProjectionLaw::Orthographic | ProjectionLaw::Isometric, RayFamily::Parallel { .. })
        | (
            ProjectionLaw::PerspectiveRay { .. } | ProjectionLaw::StereographicNorth,
            RayFamily::Central { .. },
        ) => {}
        _ => {
            return Err(ReceiverError::ProjectionSpeciesMismatch(
                specification.receiver.id,
            ));
        }
    }
    let receiver = &specification.receiver;
    let mut primitives = Vec::new();
    let mut seams = Vec::new();
    let mut field_charts = Vec::<(FrameId, RatVec3, RatVec3, RatVec3)>::new();

    for entity in construction.entities.values() {
        if admitted_entities.is_some_and(|admitted| !admitted.contains(&entity.id)) {
            continue;
        }
        let source = ReceiverPrimitiveId::Entity(entity.id);
        match &entity.geometry {
            Geometry::Triangle { vertices } => {
                field_charts.push((
                    entity.frame,
                    vertices[0].clone(),
                    vertices[1].subtract(&vertices[0]),
                    vertices[2].subtract(&vertices[0]),
                ));
                let mut projected = Vec::with_capacity(vertices.len());
                let mut contacted = false;
                for (ordinal, point) in vertices.iter().enumerate() {
                    let point = transported_point(construction, receiver, entity.frame, point)?;
                    match specification.rays.project_point(&point) {
                        Ok(projected_point) => projected
                            .push((projected_point, specification.rays.project_depth(&point)?)),
                        Err(ReceiverError::ZeroProjectivePoint) => {
                            seams.push(ArrangementSeam::ReceiverPointContact { source, ordinal });
                            contacted = true;
                        }
                        Err(error) => return Err(error),
                    }
                }
                if contacted {
                    continue;
                }
                let projected_vertices = [
                    projected[0].0.clone(),
                    projected[1].0.clone(),
                    projected[2].0.clone(),
                ];
                let receiver_depths = [
                    projected[0].1.clone(),
                    projected[1].1.clone(),
                    projected[2].1.clone(),
                ];
                primitives.push(ReceiverPrimitive::Triangle(ProjectedTriangle {
                    source,
                    receiver_depth: triangle_depth_law(
                        &specification.rays,
                        &projected_vertices,
                        &receiver_depths,
                    )
                    .map(Box::new),
                    vertices: projected_vertices,
                    receiver_depths,
                }));
            }
            Geometry::Thread { vertices, closed } => {
                if vertices.len() >= 3 {
                    let first = vertices[1].subtract(&vertices[0]);
                    let second = vertices[2].subtract(&vertices[0]);
                    if !first.cross(&second).norm_squared().is_zero() {
                        field_charts.push((entity.frame, vertices[0].clone(), first, second));
                    }
                }
                let mut projected = Vec::with_capacity(vertices.len());
                let mut contacted = false;
                for (ordinal, point) in vertices.iter().enumerate() {
                    let point = transported_point(construction, receiver, entity.frame, point)?;
                    match specification.rays.project_point(&point) {
                        Ok(projected_point) => projected
                            .push((projected_point, specification.rays.project_depth(&point)?)),
                        Err(ReceiverError::ZeroProjectivePoint) => {
                            seams.push(ArrangementSeam::ReceiverPointContact { source, ordinal });
                            contacted = true;
                        }
                        Err(error) => return Err(error),
                    }
                }
                if contacted {
                    continue;
                }
                primitives.push(ReceiverPrimitive::Thread(ProjectedThread {
                    source,
                    vertices: projected.iter().map(|point| point.0.clone()).collect(),
                    receiver_depths: projected.into_iter().map(|point| point.1).collect(),
                    closed: *closed,
                }));
            }
            Geometry::Conic(conic) => {
                field_charts.push((
                    entity.frame,
                    conic.center.clone(),
                    conic.axis_u.clone(),
                    conic.axis_v.clone(),
                ));
                let origin =
                    transported_point(construction, receiver, entity.frame, &conic.center)?;
                let axis_x =
                    transported_direction(construction, receiver, entity.frame, &conic.axis_u)?;
                let axis_y =
                    transported_direction(construction, receiver, entity.frame, &conic.axis_v)?;
                let intrinsic = conic.intrinsic_form();
                let form = HomogeneousConic::new([
                    intrinsic.rows[0][0].clone(),
                    Rat::zero(),
                    intrinsic.rows[1][1].clone(),
                    Rat::zero(),
                    Rat::zero(),
                    intrinsic.rows[2][2].clone(),
                ])?;
                match project_conic(
                    source,
                    &origin,
                    &axis_x,
                    &axis_y,
                    &form,
                    &specification.rays,
                ) {
                    Ok(projected) => primitives.push(ReceiverPrimitive::Conic(projected)),
                    Err(ReceiverError::CollapsedConicProjection) => {
                        seams.push(ArrangementSeam::ProjectionCollapsed { source });
                    }
                    Err(error) => return Err(error),
                }
            }
        }
    }

    if let Some(conics) = conics {
        for conic in conics.cells.values() {
            if admitted_conics.is_some_and(|admitted| !admitted.contains(&conic.id)) {
                continue;
            }
            field_charts.push((
                conic.frame,
                conic.chart.origin.clone(),
                conic.chart.axis_x.clone(),
                conic.chart.axis_y.clone(),
            ));
            let source = ReceiverPrimitiveId::NativeConic(conic.id);
            let origin =
                transported_point(construction, receiver, conic.frame, &conic.chart.origin)?;
            let axis_x =
                transported_direction(construction, receiver, conic.frame, &conic.chart.axis_x)?;
            let axis_y =
                transported_direction(construction, receiver, conic.frame, &conic.chart.axis_y)?;
            match project_conic(
                source,
                &origin,
                &axis_x,
                &axis_y,
                &conic.form,
                &specification.rays,
            ) {
                Ok(projected) => primitives.push(ReceiverPrimitive::Conic(projected)),
                Err(ReceiverError::CollapsedConicProjection) => {
                    seams.push(ArrangementSeam::ProjectionCollapsed { source });
                }
                Err(error) => return Err(error),
            }
        }
    }

    primitives.sort_by_key(ReceiverPrimitive::id);
    let coordinate_fields = field_charts
        .into_iter()
        .filter_map(|(frame, origin, axis_x, axis_y)| {
            match transported_coordinate_field(
                construction,
                receiver,
                frame,
                &origin,
                &axis_x,
                &axis_y,
                &specification.rays,
            ) {
                Ok(field) => Some(Ok(field)),
                Err(
                    ReceiverError::CollapsedConicProjection | ReceiverError::ZeroProjectivePoint,
                ) => {
                    seams.push(ArrangementSeam::CoordinateFieldCollapsed { frame });
                    None
                }
                Err(error) => Some(Err(error)),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let linear_pieces = linear_pieces(&primitives, &mut seams);
    let relations = if form_crossing_atlas {
        arrangement_relations_with_cpu(&linear_pieces, &primitives, executor)?.0
    } else {
        Vec::new()
    };

    Ok(ReceiverFace {
        schema: if form_crossing_atlas {
            "holonic-engine.receiver-face.v2"
        } else {
            "holonic-engine.receiver-support-face.v1"
        }
        .to_owned(),
        receiver: receiver.id,
        extent: specification.extent.clone(),
        rays: specification.rays.clone(),
        acceptance: specification.acceptance.clone(),
        arrangement: ReceiverArrangement {
            primitives,
            coordinate_fields,
            linear_pieces,
            relations,
            seams,
        },
        implicit_tori: Vec::new(),
    })
}

fn transported_coordinate_field(
    construction: &Construction,
    receiver: &Receiver,
    frame: FrameId,
    chart_origin: &RatVec3,
    chart_x: &RatVec3,
    chart_y: &RatVec3,
    rays: &RayFamily,
) -> Result<TransportedCoordinateField, ReceiverError> {
    let origin = transported_point(construction, receiver, frame, chart_origin)?;
    let axis_x = transported_direction(construction, receiver, frame, chart_x)?;
    let axis_y = transported_direction(construction, receiver, frame, chart_y)?;
    let map = projective_matrix_from_columns(
        &rays.project_direction(&axis_x)?,
        &rays.project_direction(&axis_y)?,
        &rays.project_point(&origin)?,
    );
    let inverse_transpose = map
        .inverse()
        .ok_or(ReceiverError::CollapsedConicProjection)?
        .transpose();
    let line = |source: RatVec3| {
        let line = inverse_transpose.apply(&source);
        ProjectiveLine2 {
            a: line.x,
            b: line.y,
            c: line.z,
        }
    };
    Ok(TransportedCoordinateField {
        source_frame: frame,
        // x=t is [1,0,-t], y=t is [0,1,-t].
        first_axis: ProjectiveLineFamily {
            zero: line(RatVec3::from_i64(1, 0, 0)),
            coefficient: line(RatVec3::from_i64(0, 0, -1)),
        },
        second_axis: ProjectiveLineFamily {
            zero: line(RatVec3::from_i64(0, 1, 0)),
            coefficient: line(RatVec3::from_i64(0, 0, -1)),
        },
    })
}

pub(crate) fn linear_pieces(
    primitives: &[ReceiverPrimitive],
    seams: &mut Vec<ArrangementSeam>,
) -> Vec<LinearPiece> {
    let mut pieces = Vec::new();
    for primitive in primitives {
        let (source, vertices, closed) = match primitive {
            ReceiverPrimitive::Triangle(triangle) => {
                (triangle.source, triangle.vertices.to_vec(), true)
            }
            ReceiverPrimitive::Thread(thread) => {
                (thread.source, thread.vertices.clone(), thread.closed)
            }
            ReceiverPrimitive::Conic(_) => continue,
        };
        let edge_count =
            vertices.len().saturating_sub(1) + usize::from(closed && vertices.len() > 1);
        for ordinal in 0..edge_count {
            let start = vertices[ordinal].clone();
            let end = vertices[(ordinal + 1) % vertices.len()].clone();
            let support = start.cross(&end);
            if support.a.is_zero() && support.b.is_zero() && support.c.is_zero() {
                seams.push(ArrangementSeam::ProjectionCollapsed { source });
                continue;
            }
            pieces.push(LinearPiece {
                primitive: source,
                ordinal,
                start,
                end,
                support,
            });
        }
    }
    pieces
}

pub(crate) fn arrangement_relations_with_cpu(
    linear: &[LinearPiece],
    primitives: &[ReceiverPrimitive],
    executor: &CpuExecutor,
) -> Result<(Vec<ArrangementRelation>, CpuExecutionReceipt), ReceiverError> {
    let primitive_ordinals = primitives
        .iter()
        .enumerate()
        .map(|(ordinal, primitive)| (primitive.id(), ordinal))
        .collect::<BTreeMap<_, _>>();
    let indexed_linear = linear
        .iter()
        .cloned()
        .map(|piece| (primitive_ordinals[&piece.primitive], piece))
        .collect::<Vec<_>>();
    let indexed_conics = primitives
        .iter()
        .enumerate()
        .filter_map(|(ordinal, primitive)| match primitive {
            ReceiverPrimitive::Conic(conic) => Some((ordinal, conic)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let (indexed, receipt) =
        indexed_arrangement_relations_with_cpu(&indexed_linear, &indexed_conics, None, executor)?;
    Ok((
        indexed
            .into_iter()
            .map(|(_, _, relation)| relation)
            .collect(),
        receipt,
    ))
}

/// Form one complete arrangement from primitive instances whose source
/// identities may recur in different receiver charts. The instance ordinal,
/// not the source label, carries that distinction through parallel conduct.
type IndexedArrangementRelation = (usize, usize, ArrangementRelation);
type IndexedArrangementResult =
    Result<(Vec<IndexedArrangementRelation>, CpuExecutionReceipt), ReceiverError>;

pub(crate) fn indexed_arrangement_relations_with_cpu(
    linear: &[(usize, LinearPiece)],
    conics: &[(usize, &ProjectedConic)],
    distinct_groups: Option<&[ReceiverId]>,
    executor: &CpuExecutor,
) -> IndexedArrangementResult {
    #[derive(Clone, Copy)]
    enum RelationTask {
        LinearLinear(usize, usize),
        LinearConic(usize, usize),
        ConicConic(usize, usize),
    }
    let mut tasks = Vec::new();
    for left_index in 0..linear.len() {
        for right_index in (left_index + 1)..linear.len() {
            if distinct_groups
                .is_none_or(|groups| groups[linear[left_index].0] != groups[linear[right_index].0])
            {
                tasks.push(RelationTask::LinearLinear(left_index, right_index));
            }
        }
        for conic_index in 0..conics.len() {
            if distinct_groups
                .is_none_or(|groups| groups[linear[left_index].0] != groups[conics[conic_index].0])
            {
                tasks.push(RelationTask::LinearConic(left_index, conic_index));
            }
        }
    }
    for left_index in 0..conics.len() {
        for right_index in (left_index + 1)..conics.len() {
            if distinct_groups
                .is_none_or(|groups| groups[conics[left_index].0] != groups[conics[right_index].0])
            {
                tasks.push(RelationTask::ConicConic(left_index, right_index));
            }
        }
    }
    let (partial, receipt) = executor
        .execute_indexed(&tasks, |_index, task| {
            let mut relations = Vec::new();
            match *task {
                RelationTask::LinearLinear(left_index, right_index) => {
                    let (left_primitive, left) = &linear[left_index];
                    let (right_primitive, right) = &linear[right_index];
                    if let Some(point) = left.support.cross(&right.support) {
                        relations.push((
                            *left_primitive,
                            *right_primitive,
                            ArrangementRelation::LinearCrossing {
                                left: Box::new(left.clone()),
                                right: Box::new(right.clone()),
                                left_membership: point_membership(left, &point),
                                right_membership: point_membership(right, &point),
                                point,
                            },
                        ));
                    }
                }
                RelationTask::LinearConic(linear_index, conic_index) => {
                    let (linear_primitive, linear) = &linear[linear_index];
                    let (conic_primitive, conic) = conics[conic_index];
                    let (origin, direction) = affine_segment(linear);
                    if let (Some(origin), Some(direction)) = (origin, direction) {
                        match conic.form.restrict_line(&origin, &direction)? {
                            ConicLineRelation::Coincident => {
                                relations.push((
                                    *linear_primitive,
                                    conic_primitive,
                                    ArrangementRelation::CoincidentLinearConic {
                                        linear: Box::new(linear.clone()),
                                        conic: conic.source,
                                    },
                                ));
                            }
                            ConicLineRelation::Finite(roots) => {
                                for ConicRoot {
                                    parameter,
                                    multiplicity,
                                    hand,
                                } in roots
                                {
                                    relations.push((
                                        *linear_primitive,
                                        conic_primitive,
                                        ArrangementRelation::LinearConicCrossing {
                                            linear: Box::new(linear.clone()),
                                            conic: conic.source,
                                            membership: exact_value_membership(&parameter),
                                            parameter,
                                            multiplicity,
                                            hand,
                                        },
                                    ));
                                }
                            }
                        }
                    }
                }
                RelationTask::ConicConic(left_index, right_index) => {
                    let (left_primitive, left) = conics[left_index];
                    let (right_primitive, right) = conics[right_index];
                    relations.push((
                        left_primitive,
                        right_primitive,
                        ArrangementRelation::ConicConicPencil {
                            left: left.source,
                            right: right.source,
                            left_form: Box::new(left.form.clone()),
                            right_form: Box::new(right.form.clone()),
                        },
                    ));
                }
            }
            Ok::<_, ReceiverError>(relations)
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => ReceiverError::WorkerPanicked,
        })?;
    Ok((partial.into_iter().flatten().collect(), receipt))
}

fn affine_segment(piece: &LinearPiece) -> (Option<[Rat; 2]>, Option<[Rat; 2]>) {
    let Some(start) = piece.start.affine() else {
        return (None, None);
    };
    let Some(end) = piece.end.affine() else {
        return (None, None);
    };
    let direction = [&end[0] - &start[0], &end[1] - &start[1]];
    (Some(start), Some(direction))
}

fn point_membership(piece: &LinearPiece, point: &ProjectivePoint2) -> ExactSegmentMembership {
    let (Some(start), Some(direction)) = affine_segment(piece) else {
        return ExactSegmentMembership::Open;
    };
    let Some(point) = point.affine() else {
        return ExactSegmentMembership::Outside;
    };
    let parameter = if !direction[0].is_zero() {
        (&point[0] - &start[0]) / &direction[0]
    } else if !direction[1].is_zero() {
        (&point[1] - &start[1]) / &direction[1]
    } else {
        return ExactSegmentMembership::Open;
    };
    rational_membership(&parameter)
}

fn rational_membership(parameter: &Rat) -> ExactSegmentMembership {
    if parameter < &Rat::zero() || parameter > &Rat::one() {
        ExactSegmentMembership::Outside
    } else if parameter.is_zero() || parameter.is_one() {
        ExactSegmentMembership::Boundary
    } else {
        ExactSegmentMembership::Interior
    }
}

fn exact_value_membership(parameter: &ExactValue) -> ExactSegmentMembership {
    if let Some(parameter) = parameter.as_rational() {
        return rational_membership(&parameter);
    }
    let zero = ExactValue::rational(Rat::zero());
    let one = ExactValue::rational(Rat::one());
    match (parameter.compare(&zero), parameter.compare(&one)) {
        (ExactOrdering::Less, _) | (_, ExactOrdering::Greater) => ExactSegmentMembership::Outside,
        (ExactOrdering::Equal, _) | (_, ExactOrdering::Equal) => ExactSegmentMembership::Boundary,
        (ExactOrdering::Greater, ExactOrdering::Less) => ExactSegmentMembership::Interior,
        _ => ExactSegmentMembership::Open,
    }
}

impl ReceiverFace {
    /// Query one exact receiver-local coordinate after the continuous face
    /// has already been formed.  This is useful for an input event or proof
    /// query; it is not a rendering loop.
    pub fn receive(&self, coordinate: [Rat; 2]) -> Result<FaceFiber, ReceiverError> {
        if !self.extent.contains(&coordinate) {
            return Err(ReceiverError::CoordinateOutsideFace(self.receiver));
        }
        self.receive_affine_direction(coordinate)
    }

    /// Query an affine direction of the complete continuous arrangement.
    ///
    /// Unlike `receive`, this internal operation is not clipped to the finite
    /// port aperture. It is used only by the receiver's own acceptance cover,
    /// whose directions were caused before that finite observation boundary
    /// was selected.
    fn receive_affine_direction(&self, coordinate: [Rat; 2]) -> Result<FaceFiber, ReceiverError> {
        let ray = self.rays.ray(&coordinate);
        let surface_crossings = self
            .arrangement
            .primitives
            .iter()
            .filter_map(|primitive| match primitive {
                ReceiverPrimitive::Triangle(triangle) => {
                    let ReceiverPrimitiveId::Entity(entity) = triangle.source else {
                        return None;
                    };
                    let (local_ray, local_triangle) =
                        receiver_local_triangle_query(&self.rays, &coordinate, triangle)?;
                    ray_triangle_crossing(&local_ray, entity, &local_triangle)
                }
                _ => None,
            })
            .collect();
        let point = ProjectivePoint2::new(coordinate[0].clone(), coordinate[1].clone(), Rat::one())
            .expect("an affine face coordinate is a nonzero projective point");
        let mut curve_crossings = Vec::new();
        for primitive in &self.arrangement.primitives {
            match primitive {
                ReceiverPrimitive::Thread(thread) => {
                    let segment_count = thread
                        .vertices
                        .len()
                        .saturating_sub(1)
                        .saturating_add(usize::from(thread.closed && thread.vertices.len() > 1));
                    for segment in 0..segment_count {
                        let next = (segment + 1) % thread.vertices.len();
                        let Some(parameter) = projective_segment_parameter(
                            &thread.vertices[segment],
                            &thread.vertices[next],
                            &point,
                        ) else {
                            continue;
                        };
                        let Some(depth) = interpolated_thread_depth(
                            &self.rays,
                            &parameter,
                            &thread.receiver_depths[segment],
                            &thread.receiver_depths[next],
                        ) else {
                            continue;
                        };
                        curve_crossings.push(CurveCrossing {
                            primitive: thread.source,
                            ray_parameter: depth,
                            kind: CurveCrossingKind::Thread { segment, parameter },
                        });
                    }
                }
                ReceiverPrimitive::Conic(conic)
                    if conic.form.evaluate(&[
                        coordinate[0].clone(),
                        coordinate[1].clone(),
                        Rat::one(),
                    ]) == Rat::zero() =>
                {
                    if let Some(depth) = conic.receiver_depth.evaluate(&point) {
                        curve_crossings.push(CurveCrossing {
                            primitive: conic.source,
                            ray_parameter: depth,
                            kind: CurveCrossingKind::Conic,
                        });
                    }
                }
                ReceiverPrimitive::Triangle(_) | ReceiverPrimitive::Conic(_) => {}
            }
        }
        let mut layers = crossing_layers(surface_crossings);
        for crossing in curve_crossings {
            match layers.binary_search_by(|layer| layer.ray_parameter.cmp(&crossing.ray_parameter))
            {
                Ok(index) => layers[index].curve_crossings.push(crossing),
                Err(index) => layers.insert(
                    index,
                    CrossingLayer {
                        ray_parameter: crossing.ray_parameter.clone(),
                        crossings: Vec::new(),
                        curve_crossings: vec![crossing],
                    },
                ),
            }
        }
        for layer in &mut layers {
            layer.curve_crossings.sort_by(|left, right| {
                left.primitive
                    .cmp(&right.primitive)
                    .then_with(|| match (&left.kind, &right.kind) {
                        (
                            CurveCrossingKind::Thread { segment: left, .. },
                            CurveCrossingKind::Thread { segment: right, .. },
                        ) => left.cmp(right),
                        (CurveCrossingKind::Conic, CurveCrossingKind::Thread { .. }) => {
                            Ordering::Less
                        }
                        (CurveCrossingKind::Thread { .. }, CurveCrossingKind::Conic) => {
                            Ordering::Greater
                        }
                        (CurveCrossingKind::Conic, CurveCrossingKind::Conic) => Ordering::Equal,
                    })
            });
        }
        let implicit_fibers = self
            .implicit_tori
            .iter()
            .map(|torus| torus.ray_fiber_all(&ray.origin, &ray.direction))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(FaceFiber {
            face_coordinate: coordinate,
            ray,
            layers,
            implicit_fibers,
        })
    }

    /// Receive one exact relative direction through the already-formed
    /// continuous support arrangement.
    pub fn receive_direction(
        &self,
        direction: RatVec3,
    ) -> Result<ReceiverDirectionalFiber, ReceiverError> {
        if direction == RatVec3::zero() {
            return Ok(ReceiverDirectionalFiber::SingularDirection { direction });
        }
        let coordinate = self.rays.project_direction(&direction)?;
        if let Some(affine) = coordinate.affine() {
            return Ok(ReceiverDirectionalFiber::Finite(Box::new(
                self.receive_affine_direction(affine)?,
            )));
        }

        let ray = match &self.rays {
            RayFamily::Central { center, .. } => ExactRay {
                origin: center.clone(),
                direction: direction.clone(),
            },
            RayFamily::Parallel { face_center, .. } => ExactRay {
                origin: face_center.clone(),
                direction: direction.clone(),
            },
        };
        let line_contains = |line: &ProjectiveLine2| {
            &line.a * &coordinate.x + &line.b * &coordinate.y + &line.c * &coordinate.w
                == Rat::zero()
        };
        let mut contacts = self
            .arrangement
            .linear_pieces
            .iter()
            .filter(|piece| line_contains(&piece.support))
            .map(|piece| ReceiverHorizonContact::Linear {
                primitive: piece.primitive,
                ordinal: piece.ordinal,
            })
            .collect::<Vec<_>>();
        contacts.extend(self.arrangement.primitives.iter().filter_map(
            |primitive| match primitive {
                ReceiverPrimitive::Conic(conic)
                    if conic.form.evaluate(&[
                        coordinate.x.clone(),
                        coordinate.y.clone(),
                        coordinate.w.clone(),
                    ]) == Rat::zero() =>
                {
                    Some(ReceiverHorizonContact::Conic {
                        primitive: conic.source,
                    })
                }
                ReceiverPrimitive::Triangle(_)
                | ReceiverPrimitive::Thread(_)
                | ReceiverPrimitive::Conic(_) => None,
            },
        ));
        contacts.sort_by(|left, right| {
            let key = |contact: &ReceiverHorizonContact| match contact {
                ReceiverHorizonContact::Linear { primitive, ordinal } => {
                    (*primitive, 0_u8, *ordinal)
                }
                ReceiverHorizonContact::Conic { primitive } => (*primitive, 1_u8, 0),
            };
            key(left).cmp(&key(right))
        });
        contacts.dedup();
        let implicit_fibers = self
            .implicit_tori
            .iter()
            .map(|torus| torus.ray_fiber_all(&ray.origin, &ray.direction))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ReceiverDirectionalFiber::ProjectiveHorizon(Box::new(
            ReceiverProjectiveHorizonFiber {
                direction,
                coordinate,
                ray,
                contacts,
                implicit_fibers,
            },
        )))
    }

    /// Compute every organ-center and overlap-seam fiber of the contemporary
    /// receiver cover before any terminal address descent.
    pub fn receive_acceptance_section(&self) -> Result<ReceiverAcceptanceSection, ReceiverError> {
        let cover = self
            .acceptance
            .as_ref()
            .ok_or(ReceiverError::MissingAcceptanceCover(self.receiver))?;
        let organs = cover
            .organs
            .iter()
            .map(|organ| {
                Ok(ReceiverOrganSection {
                    face: organ.face,
                    fiber: self.receive_direction(organ.central_direction.clone())?,
                })
            })
            .collect::<Result<Vec<_>, ReceiverError>>()?;
        let seams = cover
            .seams
            .iter()
            .map(|seam| {
                Ok(ReceiverSeamSection {
                    vertex: seam.vertex,
                    fiber: self.receive_direction(seam.direction.clone())?,
                })
            })
            .collect::<Result<Vec<_>, ReceiverError>>()?;
        Ok(ReceiverAcceptanceSection {
            event: cover.event,
            receiver: cover.receiver,
            organs,
            seams,
        })
    }
}

fn projective_segment_parameter(
    start: &ProjectivePoint2,
    end: &ProjectivePoint2,
    point: &ProjectivePoint2,
) -> Option<Rat> {
    let start = start.affine()?;
    let end = end.affine()?;
    let point = point.affine()?;
    let direction = [&end[0] - &start[0], &end[1] - &start[1]];
    let parameter = if !direction[0].is_zero() {
        (&point[0] - &start[0]) / &direction[0]
    } else if !direction[1].is_zero() {
        (&point[1] - &start[1]) / &direction[1]
    } else {
        return None;
    };
    if &start[0] + &parameter * &direction[0] != point[0]
        || &start[1] + &parameter * &direction[1] != point[1]
        || parameter < Rat::zero()
        || parameter > Rat::one()
    {
        return None;
    }
    Some(parameter)
}

fn interpolated_thread_depth(
    rays: &RayFamily,
    parameter: &Rat,
    start: &Rat,
    end: &Rat,
) -> Option<Rat> {
    let complement = Rat::one() - parameter;
    match rays {
        RayFamily::Parallel { .. } => Some(&complement * start + parameter * end),
        RayFamily::Central { .. } => {
            let denominator = &complement * end + parameter * start;
            (!denominator.is_zero()).then(|| start * end / denominator)
        }
    }
}

/// Reconstruct the exact triangle and query ray in the receiver's own
/// three-dimensional chart.
///
/// The projective face point carries direction while `receiver_depths`
/// carries position along that direction. Reconstructing a central point
/// from both carriers keeps projective normalization from either erasing
/// depth or preserving a meaningless common scale. A parallel projection
/// carries affine face coordinates and the same independent depth carrier.
fn receiver_local_triangle_query(
    rays: &RayFamily,
    coordinate: &[Rat; 2],
    triangle: &ProjectedTriangle,
) -> Option<(ExactRay, [RatVec3; 3])> {
    match rays {
        RayFamily::Central { .. } => {
            let affine = triangle
                .vertices
                .iter()
                .map(ProjectivePoint2::affine)
                .collect::<Option<Vec<_>>>()?;
            Some((
                ExactRay {
                    origin: RatVec3::zero(),
                    direction: RatVec3::new(
                        coordinate[0].clone(),
                        coordinate[1].clone(),
                        Rat::one(),
                    ),
                },
                [
                    RatVec3::new(
                        &affine[0][0] * &triangle.receiver_depths[0],
                        &affine[0][1] * &triangle.receiver_depths[0],
                        triangle.receiver_depths[0].clone(),
                    ),
                    RatVec3::new(
                        &affine[1][0] * &triangle.receiver_depths[1],
                        &affine[1][1] * &triangle.receiver_depths[1],
                        triangle.receiver_depths[1].clone(),
                    ),
                    RatVec3::new(
                        &affine[2][0] * &triangle.receiver_depths[2],
                        &affine[2][1] * &triangle.receiver_depths[2],
                        triangle.receiver_depths[2].clone(),
                    ),
                ],
            ))
        }
        RayFamily::Parallel { .. } => {
            let affine = triangle
                .vertices
                .iter()
                .map(ProjectivePoint2::affine)
                .collect::<Option<Vec<_>>>()?;
            Some((
                ExactRay {
                    origin: RatVec3::new(coordinate[0].clone(), coordinate[1].clone(), Rat::zero()),
                    direction: RatVec3::from_i64(0, 0, 1),
                },
                [
                    RatVec3::new(
                        affine[0][0].clone(),
                        affine[0][1].clone(),
                        triangle.receiver_depths[0].clone(),
                    ),
                    RatVec3::new(
                        affine[1][0].clone(),
                        affine[1][1].clone(),
                        triangle.receiver_depths[1].clone(),
                    ),
                    RatVec3::new(
                        affine[2][0].clone(),
                        affine[2][1].clone(),
                        triangle.receiver_depths[2].clone(),
                    ),
                ],
            ))
        }
    }
}

fn sign(value: &Rat) -> i8 {
    match value.cmp(&Rat::zero()) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

fn ray_triangle_crossing(
    ray: &ExactRay,
    entity: EntityId,
    triangle: &[RatVec3; 3],
) -> Option<SurfaceCrossing> {
    let edge_one = triangle[1].subtract(&triangle[0]);
    let edge_two = triangle[2].subtract(&triangle[0]);
    let determinant = edge_one.dot(&ray.direction.cross(&edge_two));
    if determinant.is_zero() {
        return None;
    }
    let inverse = Rat::one() / &determinant;
    let source = ray.origin.subtract(&triangle[0]);
    let u = &inverse * source.dot(&ray.direction.cross(&edge_two));
    if u.is_negative() || u > Rat::one() {
        return None;
    }
    let q = source.cross(&edge_one);
    let v = &inverse * ray.direction.dot(&q);
    if v.is_negative() || &u + &v > Rat::one() {
        return None;
    }
    let ray_parameter = inverse * edge_two.dot(&q);
    if ray_parameter.is_negative() {
        return None;
    }
    Some(SurfaceCrossing {
        entity,
        ray_parameter,
        barycentric: [Rat::one() - &u - &v, u, v],
        orientation: sign(&determinant),
    })
}

fn crossing_layers(mut crossings: Vec<SurfaceCrossing>) -> Vec<CrossingLayer> {
    crossings.sort_by(|left, right| {
        left.ray_parameter
            .cmp(&right.ray_parameter)
            .then_with(|| left.entity.cmp(&right.entity))
    });
    let mut layers = Vec::<CrossingLayer>::new();
    for crossing in crossings {
        if let Some(layer) = layers.last_mut()
            && layer.ray_parameter == crossing.ray_parameter
        {
            layer.crossings.push(crossing);
        } else {
            layers.push(CrossingLayer {
                ray_parameter: crossing.ray_parameter.clone(),
                crossings: vec![crossing],
                curve_crossings: Vec::new(),
            });
        }
    }
    layers
}

#[cfg(test)]
mod tests {
    use relational_geometry::{Geometry, ProjectionLaw, integer, rat};

    use super::*;

    fn receiver(frame: FrameId) -> ReceiverFaceSpec {
        ReceiverFaceSpec {
            receiver: Receiver::new(
                ReceiverId(1),
                "inside",
                frame,
                ProjectionLaw::PerspectiveRay {
                    focal_distance: integer(1),
                },
            ),
            extent: ReceiverFaceExtent {
                horizontal_span: integer(4),
                vertical_span: integer(3),
            },
            rays: RayFamily::Central {
                center: RatVec3::zero(),
                forward: RatVec3::from_i64(0, 0, 1),
                horizontal: RatVec3::from_i64(1, 0, 0),
                vertical: RatVec3::from_i64(0, 1, 0),
            },
            acceptance: None,
        }
    }

    #[test]
    fn face_is_continuous_and_carries_triangle_conic_thread_and_coordinate_field() {
        let (mut construction, frame) = Construction::new("local");
        construction
            .add_entity(
                "triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-1, -1, 2),
                        RatVec3::from_i64(1, -1, 2),
                        RatVec3::from_i64(0, 1, 2),
                    ],
                },
            )
            .unwrap();
        construction
            .add_entity(
                "thread",
                frame,
                Geometry::Thread {
                    vertices: vec![RatVec3::from_i64(-1, 0, 1), RatVec3::from_i64(1, 0, 1)],
                    closed: false,
                },
            )
            .unwrap();
        construction
            .add_entity(
                "circle",
                frame,
                Geometry::Conic(relational_geometry::ProjectiveConic {
                    center: RatVec3::from_i64(0, 0, 2),
                    axis_u: RatVec3::from_i64(1, 0, 0),
                    axis_v: RatVec3::from_i64(0, 1, 0),
                    species: relational_geometry::ConicSpecies::Circle,
                }),
            )
            .unwrap();
        let face = receive_face(&construction, &receiver(frame)).unwrap();
        assert_eq!(face.arrangement.primitives.len(), 3);
        assert_eq!(face.arrangement.coordinate_fields.len(), 2);
        assert!(!face.arrangement.linear_pieces.is_empty());
        assert!(
            face.arrangement.relations.iter().any(|relation| matches!(
                relation,
                ArrangementRelation::LinearConicCrossing { .. }
            ))
        );
        let fiber = face
            .receive([integer(1) / integer(2), Rat::zero()])
            .unwrap();
        assert!(fiber.layers.iter().any(|layer| {
            layer
                .curve_crossings
                .iter()
                .any(|crossing| matches!(crossing.kind, CurveCrossingKind::Thread { .. }))
        }));
        assert!(fiber.layers.iter().any(|layer| {
            layer
                .curve_crossings
                .iter()
                .any(|crossing| matches!(crossing.kind, CurveCrossingKind::Conic))
        }));
    }

    #[test]
    fn selected_support_receives_only_the_intrinsic_source_section() {
        let (mut construction, frame) = Construction::new("selected local star");
        let admitted = construction
            .add_entity(
                "admitted triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-1, -1, 2),
                        RatVec3::from_i64(1, -1, 2),
                        RatVec3::from_i64(0, 1, 2),
                    ],
                },
            )
            .unwrap();
        let excluded = construction
            .add_entity(
                "exterior triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-2, -2, 4),
                        RatVec3::from_i64(2, -2, 4),
                        RatVec3::from_i64(0, 2, 4),
                    ],
                },
            )
            .unwrap();
        let specification = receiver(frame);
        let selection = ReceiverSourceSelection {
            entities: BTreeSet::from([admitted]),
            conics: BTreeSet::new(),
        };
        let source = selection
            .section(&construction, &NativeConicPopulation::default())
            .unwrap();
        assert_eq!(
            source.entities.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([admitted])
        );
        assert!(!source.entities.contains_key(&excluded));

        let (faces, _) = receive_selected_support_faces_with_conics_cpu(
            &construction,
            &NativeConicPopulation::default(),
            std::slice::from_ref(&specification),
            &BTreeMap::from([(specification.receiver.id, selection)]),
            &CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(faces.len(), 1);
        assert_eq!(faces[0].arrangement.primitives.len(), 1);
        assert_eq!(
            faces[0].arrangement.primitives[0].id(),
            ReceiverPrimitiveId::Entity(admitted)
        );
    }

    #[test]
    fn central_projection_is_exact_and_receiver_relative() {
        let rays = receiver(FrameId(1)).rays;
        assert_eq!(
            rays.project_point(&RatVec3::from_i64(1, 2, 4))
                .unwrap()
                .affine(),
            Some([rat(1, 4), rat(1, 2)])
        );
    }

    #[test]
    fn a_source_vertex_at_the_receiver_is_a_typed_contact_not_a_crash() {
        let (mut construction, frame) = Construction::new("contact");
        let entity = construction
            .add_entity(
                "contacted triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::zero(),
                        RatVec3::from_i64(1, 0, 2),
                        RatVec3::from_i64(0, 1, 2),
                    ],
                },
            )
            .unwrap();
        let face = receive_face(&construction, &receiver(frame)).unwrap();
        assert!(face.arrangement.primitives.is_empty());
        assert_eq!(
            face.arrangement.seams,
            vec![
                ArrangementSeam::ReceiverPointContact {
                    source: ReceiverPrimitiveId::Entity(entity),
                    ordinal: 0,
                },
                ArrangementSeam::CoordinateFieldCollapsed { frame },
            ]
        );
    }

    #[test]
    fn central_face_query_preserves_depth_and_orders_crossings() {
        let (mut construction, frame) = Construction::new("layered");
        let near = construction
            .add_entity(
                "near",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-1, -1, 2),
                        RatVec3::from_i64(1, -1, 2),
                        RatVec3::from_i64(0, 1, 2),
                    ],
                },
            )
            .unwrap();
        let far = construction
            .add_entity(
                "far",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-2, -2, 4),
                        RatVec3::from_i64(2, -2, 4),
                        RatVec3::from_i64(0, 2, 4),
                    ],
                },
            )
            .unwrap();

        let face = receive_face(&construction, &receiver(frame)).unwrap();
        let fiber = face.receive([Rat::zero(), Rat::zero()]).unwrap();

        assert_eq!(fiber.layers.len(), 2);
        assert_eq!(fiber.layers[0].ray_parameter, integer(2));
        assert_eq!(fiber.layers[0].crossings[0].entity, near);
        assert_eq!(fiber.layers[1].ray_parameter, integer(4));
        assert_eq!(fiber.layers[1].crossings[0].entity, far);
    }

    #[test]
    fn certified_source_owns_native_torus_and_its_quartic_first_person_fiber() {
        let (construction, frame) = Construction::new("implicit receiver");
        let specification = receiver(frame);
        let torus = ExactTorus::new(
            crate::ImplicitCellId(1),
            EventId(1),
            RatVec3::from_i64(3, 0, 5),
            RatVec3::from_i64(0, 0, 1),
            integer(3),
            integer(1),
        )
        .unwrap();
        let receiver_id = specification.receiver.id;
        let selections = BTreeMap::from([(receiver_id, ReceiverSourceSelection::default())]);
        let implicit_tori =
            BTreeMap::from([(receiver_id, BTreeMap::from([(torus.id, torus.clone())]))]);
        let (mut formed, _) = receive_selected_faces_with_implicit_tori_certified_cpu(
            EventId(2),
            &construction,
            &NativeConicPopulation::default(),
            &implicit_tori,
            std::slice::from_ref(&specification),
            &selections,
            &CpuExecutor::serial(),
        )
        .unwrap();
        let certified = formed.pop().unwrap();
        assert_eq!(
            certified.formation.source_section().implicit_tori,
            BTreeMap::from([(torus.id, torus.clone())])
        );
        assert_eq!(certified.formation.face(), &certified.face);
        assert_eq!(certified.formation.rays(), &specification.rays);
        assert_eq!(certified.face.implicit_tori, vec![torus.clone()]);

        let fiber = certified.face.receive([Rat::zero(), Rat::zero()]).unwrap();
        assert_eq!(fiber.implicit_fibers.len(), 1);
        assert_eq!(fiber.implicit_fibers[0].polynomial.degree(), 4);
        assert_eq!(fiber.implicit_fibers[0].roots.len(), 2);

        let mut moved_rays = specification.rays.clone();
        let RayFamily::Central { center, .. } = &mut moved_rays else {
            unreachable!("the test receiver is central")
        };
        *center = RatVec3::from_i64(1, 0, 0);
        assert!(
            certified
                .formation
                .source_section()
                .exact_rebase_to(
                    certified.formation.source_section(),
                    &specification.rays,
                    &moved_rays,
                )
                .is_none()
        );

        let mut future_torus = torus;
        future_torus.last_event = EventId(3);
        let future_population = BTreeMap::from([(
            receiver_id,
            BTreeMap::from([(future_torus.id, future_torus)]),
        )]);
        assert!(matches!(
            receive_selected_faces_with_implicit_tori_certified_cpu(
                EventId(2),
                &construction,
                &NativeConicPopulation::default(),
                &future_population,
                &[specification],
                &selections,
                &CpuExecutor::serial(),
            ),
            Err(ReceiverError::ImplicitSourceAfterFormation { .. })
        ));
    }
}
