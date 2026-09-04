//! Receiver-relative projection and exact crossing analysis.
//!
//! Projection is a mathematical map owned by the receiver.  The renderer
//! consumes its output; it does not own the camera relation or feed
//! approximated coordinates back into the construction.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Deserializer, Serialize};
use thiserror::Error;

use crate::exact::{ExactExpr, ExactVec2, Rat, RatMat3, RatVec2, RatVec3, integer, rat, sign};
use crate::model::{
    Construction, EntityId, FrameId, Geometry, RelationId, TransportError, describe_point,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverId(pub u64);

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

fn primitive_projective<const N: usize>(
    mut components: [BigInt; N],
) -> Result<[BigInt; N], ReceiverOrientationError> {
    let content = components
        .iter()
        .cloned()
        .reduce(integer_gcd)
        .unwrap_or_else(BigInt::zero);
    if content.is_zero() {
        return Err(ReceiverOrientationError::ZeroProjectiveCarrier);
    }
    for component in &mut components {
        *component /= &content;
    }
    if components
        .iter()
        .find(|component| !component.is_zero())
        .is_some_and(BigInt::is_negative)
    {
        for component in &mut components {
            *component = -component.clone();
        }
    }
    Ok(components)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProjectiveRatio {
    numerator: BigInt,
    denominator: BigInt,
}

#[derive(Deserialize)]
struct ProjectiveRatioWire {
    numerator: BigInt,
    denominator: BigInt,
}

impl<'de> Deserialize<'de> for ProjectiveRatio {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProjectiveRatioWire::deserialize(deserializer)?;
        Self::new(wire.numerator, wire.denominator).map_err(serde::de::Error::custom)
    }
}

impl ProjectiveRatio {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Result<Self, ReceiverOrientationError> {
        let [numerator, denominator] = primitive_projective([numerator, denominator])?;
        Ok(Self {
            numerator,
            denominator,
        })
    }

    pub fn from_rat(value: &Rat) -> Self {
        Self::new(value.numer().clone(), value.denom().clone())
            .expect("a rational is a nonzero projective pair")
    }

    pub fn zero() -> Self {
        Self {
            numerator: BigInt::zero(),
            denominator: BigInt::one(),
        }
    }

    pub fn infinity() -> Self {
        Self {
            numerator: BigInt::one(),
            denominator: BigInt::zero(),
        }
    }

    pub fn numerator(&self) -> &BigInt {
        &self.numerator
    }

    pub fn denominator(&self) -> &BigInt {
        &self.denominator
    }

    pub fn finite(&self) -> Option<Rat> {
        (!self.denominator.is_zero())
            .then(|| Rat::new(self.numerator.clone(), self.denominator.clone()))
    }

    pub fn opposite(&self) -> Self {
        Self::new(-self.numerator.clone(), self.denominator.clone())
            .expect("the opposite of a projective ratio remains nonzero")
    }

    pub fn compose_same_axis(&self, next: &Self) -> Self {
        Self::new(
            &self.numerator * &next.denominator + &self.denominator * &next.numerator,
            &self.denominator * &next.denominator - &self.numerator * &next.numerator,
        )
        .expect("two exact rotations compose to a nonzero projective ratio")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverRotationAxis {
    X,
    Y,
    Z,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactSpin {
    components: [BigInt; 4],
}

#[derive(Deserialize)]
struct ExactSpinWire {
    components: [BigInt; 4],
}

impl<'de> Deserialize<'de> for ExactSpin {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ExactSpinWire::deserialize(deserializer)?;
        Self::new(wire.components).map_err(serde::de::Error::custom)
    }
}

impl ExactSpin {
    pub fn new(components: [BigInt; 4]) -> Result<Self, ReceiverOrientationError> {
        Ok(Self {
            components: primitive_projective(components)?,
        })
    }

    pub fn identity() -> Self {
        Self {
            components: [
                BigInt::one(),
                BigInt::zero(),
                BigInt::zero(),
                BigInt::zero(),
            ],
        }
    }

    pub fn axis(axis: ReceiverRotationAxis, ratio: &ProjectiveRatio) -> Self {
        let d = ratio.denominator().clone();
        let n = ratio.numerator().clone();
        let components = match axis {
            ReceiverRotationAxis::X => [d, n, BigInt::zero(), BigInt::zero()],
            ReceiverRotationAxis::Y => [d, BigInt::zero(), n, BigInt::zero()],
            ReceiverRotationAxis::Z => [d, BigInt::zero(), BigInt::zero(), n],
        };
        Self::new(components).expect("one projective ratio emits one nonzero spin")
    }

    pub fn components(&self) -> &[BigInt; 4] {
        &self.components
    }

    pub fn multiply(&self, right: &Self) -> Self {
        let [w1, x1, y1, z1] = self.components.each_ref();
        let [w2, x2, y2, z2] = right.components.each_ref();
        Self::new([
            w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2,
            w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2,
            w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2,
            w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2,
        ])
        .expect("the product of two nonzero rational spins is nonzero")
    }

    /// Return the orientation obtained by applying `self`, then `next`.
    pub fn followed_by(&self, next: &Self) -> Self {
        next.multiply(self)
    }

    pub fn inverse(&self) -> Self {
        let [w, x, y, z] = self.components.each_ref();
        Self::new([w.clone(), -x, -y, -z]).expect("the conjugate of a nonzero spin is nonzero")
    }

    /// Exact repeated action of one elementary spin, evaluated by binary
    /// powering. The retained repetition count can therefore scale with
    /// device occurrences without replaying each occurrence.
    pub fn pow(&self, exponent: &BigUint) -> Self {
        let mut exponent = exponent.clone();
        let mut base = self.clone();
        let mut product = Self::identity();
        while !exponent.is_zero() {
            if (&exponent & BigUint::one()) == BigUint::one() {
                product = base.multiply(&product);
            }
            exponent >>= 1_usize;
            if !exponent.is_zero() {
                base = base.multiply(&base);
            }
        }
        product
    }

    pub fn matrix(&self) -> RatMat3 {
        let [w, x, y, z] = self.components.each_ref();
        let norm = w * w + x * x + y * y + z * z;
        let ratio = |numerator: BigInt| Rat::new(numerator, norm.clone());
        let two = BigInt::from(2_u8);
        RatMat3::new([
            [
                ratio(w * w + x * x - y * y - z * z),
                ratio(&two * (x * y - w * z)),
                ratio(&two * (x * z + w * y)),
            ],
            [
                ratio(&two * (x * y + w * z)),
                ratio(w * w - x * x + y * y - z * z),
                ratio(&two * (y * z - w * x)),
            ],
            [
                ratio(&two * (x * z - w * y)),
                ratio(&two * (y * z + w * x)),
                ratio(w * w - x * x - y * y + z * z),
            ],
        ])
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverOrientationError {
    #[error("an exact projective orientation carrier cannot be identically zero")]
    ZeroProjectiveCarrier,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverOrientation {
    spin: ExactSpin,
}

impl ReceiverOrientation {
    pub fn identity() -> Self {
        Self {
            spin: ExactSpin::identity(),
        }
    }

    pub fn from_spin(spin: ExactSpin) -> Self {
        Self { spin }
    }

    pub fn from_cayley_xyz(about_x: Rat, about_y: Rat, about_z: Rat) -> Self {
        let mut orientation = Self::identity();
        orientation.precess(
            ReceiverRotationAxis::X,
            &ProjectiveRatio::from_rat(&about_x),
        );
        orientation.precess(
            ReceiverRotationAxis::Y,
            &ProjectiveRatio::from_rat(&about_y),
        );
        orientation.precess(
            ReceiverRotationAxis::Z,
            &ProjectiveRatio::from_rat(&about_z),
        );
        orientation
    }

    pub fn spin(&self) -> &ExactSpin {
        &self.spin
    }

    pub fn precess(&mut self, axis: ReceiverRotationAxis, ratio: &ProjectiveRatio) {
        self.spin = self.spin.followed_by(&ExactSpin::axis(axis, ratio));
    }

    pub fn precess_cayley(&mut self, axis: ReceiverRotationAxis, parameter: &Rat) {
        self.precess(axis, &ProjectiveRatio::from_rat(parameter));
    }

    pub fn followed_by(&self, step: &ExactSpin) -> Self {
        Self {
            spin: self.spin.followed_by(step),
        }
    }

    pub fn matrix(&self) -> RatMat3 {
        self.spin.matrix()
    }
}

/// The receiver's exact local measurement convention.
///
/// `reference` is not a universal ruler. The pullback metric is divided by
/// this vector's nonzero squared face magnitude at `anchor`, so this one
/// receiver measures that reference as one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGauge {
    pub anchor: RatVec3,
    pub reference: RatVec3,
}

impl Default for ReceiverGauge {
    fn default() -> Self {
        Self {
            anchor: RatVec3::zero(),
            reference: RatVec3::from_i64(1, 0, 0),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionLaw {
    Orthographic,
    PerspectiveRay { focal_distance: Rat },
    StereographicNorth,
    Isometric,
}

impl ProjectionLaw {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Orthographic => "orthographic",
            Self::PerspectiveRay { .. } => "perspective ray",
            Self::StereographicNorth => "stereographic",
            Self::Isometric => "isometric",
        }
    }

    pub fn fiber_statement(&self) -> String {
        match self {
            Self::Orthographic => "linear fiber span{(0,0,1)}".to_owned(),
            Self::PerspectiveRay { focal_distance } => format!(
                "each face point retains the ray through focus (0,0,-{})",
                crate::exact::format_rat(focal_distance)
            ),
            Self::StereographicNorth => {
                "each face point retains its line through the north pole (0,0,1)".to_owned()
            }
            Self::Isometric => {
                "linear fiber span{(1,1,1)}; every source axis has squared scale 2/3".to_owned()
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Receiver {
    pub id: ReceiverId,
    pub name: String,
    pub frame: FrameId,
    pub orientation: ReceiverOrientation,
    pub projection: ProjectionLaw,
    #[serde(default)]
    pub gauge: ReceiverGauge,
    /// A route is required only where the relation graph admits more than
    /// one path from a source frame into this receiver.
    pub route_overrides: BTreeMap<FrameId, Vec<RelationId>>,
}

impl Receiver {
    pub fn new(
        id: ReceiverId,
        name: impl Into<String>,
        frame: FrameId,
        projection: ProjectionLaw,
    ) -> Self {
        Self {
            id,
            name: name.into(),
            frame,
            orientation: ReceiverOrientation::identity(),
            projection,
            gauge: ReceiverGauge::default(),
            route_overrides: BTreeMap::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedPoint {
    pub exact: ExactVec2,
    /// Present when the receiver map remains rational.  This is used for
    /// exact crossing tests and never stores a render approximation.
    pub rational: Option<RatVec2>,
    pub receiver_point: RatVec3,
    pub depth: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedPolyline {
    pub entity: EntityId,
    pub points: Vec<ProjectedPoint>,
    pub closed: bool,
    pub crossing_bearing: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedEntity {
    pub entity: EntityId,
    pub polylines: Vec<ProjectedPolyline>,
    pub control_points: Vec<ProjectedPoint>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedChartLine {
    pub frame: FrameId,
    pub family_axis: usize,
    pub travel_axis: usize,
    pub offset: Rat,
    pub points: Vec<ProjectedPoint>,
    pub major: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedChartLabel {
    pub text: String,
    pub point: ProjectedPoint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectedChartField {
    pub frame: FrameId,
    pub frame_name: String,
    pub plane: [usize; 2],
    pub intrinsic_gram: RatMat3,
    pub intrinsic_orientation: i8,
    pub face_gram_at_origin: RatMat3,
    pub gauge_normalized_face_gram: RatMat3,
    pub plane_discriminant: Rat,
    pub conformal_scale: Option<Rat>,
    pub lines: Vec<ProjectedChartLine>,
    pub labels: Vec<ProjectedChartLabel>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverMetric {
    pub anchor: RatVec3,
    pub reference: RatVec3,
    pub pullback: RatMat3,
    pub reference_squared: Rat,
    pub normalized: RatMat3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TriangleFaceSignature {
    pub entity: EntityId,
    pub side_squared: [Rat; 3],
    pub side_ratios: [Rat; 3],
    pub gauge_normalized_side_squared: [Rat; 3],
    pub parity: i8,
    pub signed_area_witness: ExactExpr,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ProjectionError {
    #[error(transparent)]
    Transport(#[from] TransportError),
    #[error("receiver projection is singular at the supplied point: {0}")]
    Singular(String),
    #[error("entity {0} is not present")]
    MissingEntity(EntityId),
    #[error("receiver measurement gauge is singular: {0}")]
    SingularGauge(String),
    #[error("entity {0} is not a triangle")]
    NotATriangle(EntityId),
}

pub fn project_point(
    construction: &Construction,
    source_frame: FrameId,
    point: &RatVec3,
    receiver: &Receiver,
) -> Result<ProjectedPoint, ProjectionError> {
    let transport = receiver_transport(construction, source_frame, receiver)?;
    let receiver_point = receiver.orientation.matrix().apply(&transport.apply(point));
    project_receiver_point(&receiver_point, &receiver.projection)
}

fn receiver_transport(
    construction: &Construction,
    source_frame: FrameId,
    receiver: &Receiver,
) -> Result<crate::exact::AffineMap3, TransportError> {
    if let Some(route) = receiver.route_overrides.get(&source_frame) {
        construction.transport_via(source_frame, receiver.frame, route)
    } else {
        construction.transport(source_frame, receiver.frame)
    }
}

pub fn project_receiver_point(
    point: &RatVec3,
    projection: &ProjectionLaw,
) -> Result<ProjectedPoint, ProjectionError> {
    match projection {
        ProjectionLaw::Orthographic => {
            let rational = RatVec2::new(point.x.clone(), point.y.clone());
            Ok(ProjectedPoint {
                exact: ExactVec2::new(
                    ExactExpr::from(rational.x.clone()),
                    ExactExpr::from(rational.y.clone()),
                ),
                rational: Some(rational),
                receiver_point: point.clone(),
                depth: point.z.clone(),
            })
        }
        ProjectionLaw::PerspectiveRay { focal_distance } => {
            let denominator = focal_distance + &point.z;
            if denominator.is_zero() {
                return Err(ProjectionError::Singular(
                    "the point lies on the receiver's focal plane".to_owned(),
                ));
            }
            let rational = RatVec2::new(
                focal_distance * &point.x / &denominator,
                focal_distance * &point.y / &denominator,
            );
            Ok(ProjectedPoint {
                exact: ExactVec2::new(
                    ExactExpr::from(rational.x.clone()),
                    ExactExpr::from(rational.y.clone()),
                ),
                rational: Some(rational),
                receiver_point: point.clone(),
                depth: denominator,
            })
        }
        ProjectionLaw::StereographicNorth => {
            let denominator = Rat::one() - &point.z;
            if denominator.is_zero() {
                return Err(ProjectionError::Singular(
                    "the point is the stereographic receiver pole".to_owned(),
                ));
            }
            let rational = RatVec2::new(&point.x / &denominator, &point.y / &denominator);
            Ok(ProjectedPoint {
                exact: ExactVec2::new(
                    ExactExpr::from(rational.x.clone()),
                    ExactExpr::from(rational.y.clone()),
                ),
                rational: Some(rational),
                receiver_point: point.clone(),
                depth: denominator,
            })
        }
        ProjectionLaw::Isometric => {
            let root_two = ExactExpr::sqrt_int(2);
            let root_six = ExactExpr::sqrt_int(6);
            let x = ExactExpr::from(&point.x - &point.z).divide(root_two);
            let y = ExactExpr::from(&point.x + &point.z - integer(2) * &point.y).divide(root_six);
            Ok(ProjectedPoint {
                exact: ExactVec2::new(x, y),
                rational: None,
                receiver_point: point.clone(),
                depth: &point.x + &point.y + &point.z,
            })
        }
    }
}

pub fn project_entity(
    construction: &Construction,
    entity: EntityId,
    receiver: &Receiver,
    conic_subdivisions: i64,
) -> Result<ProjectedEntity, ProjectionError> {
    let entity_row = construction
        .entities
        .get(&entity)
        .ok_or(ProjectionError::MissingEntity(entity))?;
    let project = |point: &RatVec3| project_point(construction, entity_row.frame, point, receiver);
    let control_points = entity_row
        .geometry
        .control_points()
        .iter()
        .map(project)
        .collect::<Result<Vec<_>, _>>()?;
    let polylines = match &entity_row.geometry {
        Geometry::Triangle { vertices } => vec![ProjectedPolyline {
            entity,
            points: vertices
                .iter()
                .map(project)
                .collect::<Result<Vec<_>, _>>()?,
            closed: true,
            crossing_bearing: false,
        }],
        Geometry::Conic(conic) => conic
            .exact_samples(conic_subdivisions)
            .into_iter()
            .map(|points| {
                Ok(ProjectedPolyline {
                    entity,
                    points: points
                        .iter()
                        .map(project)
                        .collect::<Result<Vec<_>, ProjectionError>>()?,
                    closed: matches!(
                        conic.species,
                        crate::model::ConicSpecies::Circle | crate::model::ConicSpecies::Ellipse
                    ),
                    crossing_bearing: false,
                })
            })
            .collect::<Result<Vec<_>, ProjectionError>>()?,
        Geometry::Thread { vertices, closed } => vec![ProjectedPolyline {
            entity,
            points: vertices
                .iter()
                .map(project)
                .collect::<Result<Vec<_>, _>>()?,
            closed: *closed,
            crossing_bearing: true,
        }],
    };
    Ok(ProjectedEntity {
        entity,
        polylines,
        control_points,
    })
}

/// Project one exact two-axis chart sheet through the same declared relation
/// and receiver law as every geometric entity.
///
/// Grid density is an instrument parameter. `step`, `radius`, and
/// `samples_per_step` never alter the carried chart or construction.
pub fn project_chart_field(
    construction: &Construction,
    frame: FrameId,
    receiver: &Receiver,
    plane: [usize; 2],
    step: &Rat,
    radius: i64,
    samples_per_step: i64,
) -> Result<ProjectedChartField, ProjectionError> {
    let local_frame = construction
        .frames
        .get(&frame)
        .ok_or(TransportError::MissingFrame(frame))?;
    assert!(plane[0] < 3 && plane[1] < 3 && plane[0] != plane[1]);
    assert!(!step.is_zero());
    assert!(radius >= 1);
    assert!(samples_per_step >= 1);

    let mut lines = Vec::new();
    for (family_axis, travel_axis) in [(plane[0], plane[1]), (plane[1], plane[0])] {
        for offset_index in -radius..=radius {
            let offset = integer(offset_index) * step;
            let mut segment = Vec::new();
            let sample_radius = radius * samples_per_step;
            for sample_index in -sample_radius..=sample_radius {
                let travel = integer(sample_index) * step / integer(samples_per_step);
                let mut components = RatVec3::zero();
                set_component(&mut components, family_axis, offset.clone());
                set_component(&mut components, travel_axis, travel);
                let point = local_frame.chart.point(&components);
                match project_point(construction, frame, &point, receiver) {
                    Ok(projected) => segment.push(projected),
                    Err(ProjectionError::Singular(_)) => {
                        push_chart_segment(
                            &mut lines,
                            frame,
                            family_axis,
                            travel_axis,
                            &offset,
                            &mut segment,
                        );
                    }
                    Err(error) => return Err(error),
                }
            }
            push_chart_segment(
                &mut lines,
                frame,
                family_axis,
                travel_axis,
                &offset,
                &mut segment,
            );
        }
    }

    let mut labels = Vec::new();
    if let Ok(origin) = project_point(construction, frame, &local_frame.chart.origin, receiver) {
        labels.push(ProjectedChartLabel {
            text: format!("frame {} · {}", local_frame.id, local_frame.name),
            point: origin,
        });
    }
    for axis in 0..3 {
        let endpoint = local_frame.chart.origin.add(&local_frame.chart.basis[axis]);
        if let Ok(point) = project_point(construction, frame, &endpoint, receiver) {
            labels.push(ProjectedChartLabel {
                text: format!("f{}:{}=1", frame.0, local_frame.chart.labels[axis]),
                point,
            });
        }
    }

    let intrinsic_gram = local_frame.chart.gram();
    let transport = receiver_transport(construction, frame, receiver)?;
    let orientation = receiver.orientation.matrix();
    let receiver_origin = orientation.apply(&transport.apply(&local_frame.chart.origin));
    let projection_gram = projection_pullback_gram(&receiver_origin, &receiver.projection)?;
    let chart_to_receiver = orientation
        .multiply(&transport.linear)
        .multiply(&local_frame.chart.basis_matrix());
    let face_gram_at_origin = chart_to_receiver
        .transpose()
        .multiply(&projection_gram)
        .multiply(&chart_to_receiver);
    let receiver_unit_squared = receiver_metric(receiver)?.reference_squared;
    let gauge_normalized_face_gram =
        face_gram_at_origin.scale(&(Rat::one() / receiver_unit_squared));
    let first = plane[0];
    let second = plane[1];
    let plane_discriminant = &face_gram_at_origin.rows[first][first]
        * &face_gram_at_origin.rows[second][second]
        - &face_gram_at_origin.rows[first][second] * &face_gram_at_origin.rows[second][first];
    let conformal_scale =
        proportional_on_plane(&intrinsic_gram, &face_gram_at_origin, first, second);

    Ok(ProjectedChartField {
        frame,
        frame_name: local_frame.name.clone(),
        plane,
        intrinsic_gram,
        intrinsic_orientation: local_frame.chart.orientation(),
        face_gram_at_origin,
        gauge_normalized_face_gram,
        plane_discriminant,
        conformal_scale,
        lines,
        labels,
    })
}

fn proportional_on_plane(
    source: &RatMat3,
    target: &RatMat3,
    first: usize,
    second: usize,
) -> Option<Rat> {
    let entries = [
        (first, first),
        (first, second),
        (second, first),
        (second, second),
    ];
    let (pivot_row, pivot_column) = entries
        .iter()
        .copied()
        .find(|(row, column)| !source.rows[*row][*column].is_zero())?;
    let scale = &target.rows[pivot_row][pivot_column] / &source.rows[pivot_row][pivot_column];
    entries
        .iter()
        .all(|(row, column)| target.rows[*row][*column] == &source.rows[*row][*column] * &scale)
        .then_some(scale)
}

fn set_component(vector: &mut RatVec3, axis: usize, value: Rat) {
    match axis {
        0 => vector.x = value,
        1 => vector.y = value,
        2 => vector.z = value,
        _ => unreachable!("a rank-three chart has exactly three axes"),
    }
}

fn push_chart_segment(
    lines: &mut Vec<ProjectedChartLine>,
    frame: FrameId,
    family_axis: usize,
    travel_axis: usize,
    offset: &Rat,
    points: &mut Vec<ProjectedPoint>,
) {
    if points.len() >= 2 {
        lines.push(ProjectedChartLine {
            frame,
            family_axis,
            travel_axis,
            offset: offset.clone(),
            points: std::mem::take(points),
            major: offset.is_zero() || offset.denom().is_one(),
        });
    } else {
        points.clear();
    }
}

pub fn receiver_metric(receiver: &Receiver) -> Result<ReceiverMetric, ProjectionError> {
    let orientation = receiver.orientation.matrix();
    let oriented_anchor = orientation.apply(&receiver.gauge.anchor);
    let projection_gram = projection_pullback_gram(&oriented_anchor, &receiver.projection)?;
    let pullback = orientation
        .transpose()
        .multiply(&projection_gram)
        .multiply(&orientation);
    let reference_squared = pullback.bilinear(&receiver.gauge.reference, &receiver.gauge.reference);
    if reference_squared.is_zero() {
        return Err(ProjectionError::SingularGauge(format!(
            "reference {} lies in the receiver fiber at anchor {}",
            describe_point(&receiver.gauge.reference),
            describe_point(&receiver.gauge.anchor)
        )));
    }
    let normalized = pullback.scale(&(Rat::one() / &reference_squared));
    Ok(ReceiverMetric {
        anchor: receiver.gauge.anchor.clone(),
        reference: receiver.gauge.reference.clone(),
        pullback,
        reference_squared,
        normalized,
    })
}

fn projection_pullback_gram(
    point: &RatVec3,
    projection: &ProjectionLaw,
) -> Result<RatMat3, ProjectionError> {
    match projection {
        ProjectionLaw::Orthographic => Ok(RatMat3::from_i64([[1, 0, 0], [0, 1, 0], [0, 0, 0]])),
        ProjectionLaw::PerspectiveRay { focal_distance } => {
            let denominator = focal_distance + &point.z;
            if denominator.is_zero() {
                return Err(ProjectionError::Singular(
                    "the gauge anchor lies on the receiver's focal plane".to_owned(),
                ));
            }
            let denominator_squared = &denominator * &denominator;
            let row_x = RatVec3::new(
                focal_distance / &denominator,
                Rat::zero(),
                -(focal_distance * &point.x / &denominator_squared),
            );
            let row_y = RatVec3::new(
                Rat::zero(),
                focal_distance / &denominator,
                -(focal_distance * &point.y / denominator_squared),
            );
            Ok(gram_from_rows(&row_x, &row_y))
        }
        ProjectionLaw::StereographicNorth => {
            let denominator = Rat::one() - &point.z;
            if denominator.is_zero() {
                return Err(ProjectionError::Singular(
                    "the gauge anchor is the stereographic receiver pole".to_owned(),
                ));
            }
            let denominator_squared = &denominator * &denominator;
            let row_x = RatVec3::new(
                Rat::one() / &denominator,
                Rat::zero(),
                &point.x / &denominator_squared,
            );
            let row_y = RatVec3::new(
                Rat::zero(),
                Rat::one() / &denominator,
                &point.y / denominator_squared,
            );
            Ok(gram_from_rows(&row_x, &row_y))
        }
        ProjectionLaw::Isometric => Ok(RatMat3::new([
            [rat(2, 3), rat(-1, 3), rat(-1, 3)],
            [rat(-1, 3), rat(2, 3), rat(-1, 3)],
            [rat(-1, 3), rat(-1, 3), rat(2, 3)],
        ])),
    }
}

fn gram_from_rows(first: &RatVec3, second: &RatVec3) -> RatMat3 {
    let entry = |left: &Rat, right: &Rat, other_left: &Rat, other_right: &Rat| {
        left * right + other_left * other_right
    };
    RatMat3::new([
        [
            entry(&first.x, &first.x, &second.x, &second.x),
            entry(&first.x, &first.y, &second.x, &second.y),
            entry(&first.x, &first.z, &second.x, &second.z),
        ],
        [
            entry(&first.y, &first.x, &second.y, &second.x),
            entry(&first.y, &first.y, &second.y, &second.y),
            entry(&first.y, &first.z, &second.y, &second.z),
        ],
        [
            entry(&first.z, &first.x, &second.z, &second.x),
            entry(&first.z, &first.y, &second.z, &second.y),
            entry(&first.z, &first.z, &second.z, &second.z),
        ],
    ])
}

pub fn triangle_face_signature(
    construction: &Construction,
    entity: EntityId,
    receiver: &Receiver,
) -> Result<TriangleFaceSignature, ProjectionError> {
    let row = construction
        .entities
        .get(&entity)
        .ok_or(ProjectionError::MissingEntity(entity))?;
    let Geometry::Triangle { vertices } = &row.geometry else {
        return Err(ProjectionError::NotATriangle(entity));
    };
    let points = vertices
        .iter()
        .map(|point| project_point(construction, row.frame, point, receiver))
        .collect::<Result<Vec<_>, _>>()?;

    let (side_squared, signed_area_witness, parity) =
        if matches!(receiver.projection, ProjectionLaw::Isometric) {
            let gram = projection_pullback_gram(&RatVec3::zero(), &ProjectionLaw::Isometric)?;
            let edge_01 = points[1].receiver_point.subtract(&points[0].receiver_point);
            let edge_12 = points[2].receiver_point.subtract(&points[1].receiver_point);
            let edge_20 = points[0].receiver_point.subtract(&points[2].receiver_point);
            let edge_02 = points[2].receiver_point.subtract(&points[0].receiver_point);
            let first_a = &edge_01.x - &edge_01.z;
            let first_b = &edge_01.x + &edge_01.z - integer(2) * &edge_01.y;
            let second_a = &edge_02.x - &edge_02.z;
            let second_b = &edge_02.x + &edge_02.z - integer(2) * &edge_02.y;
            let area_numerator = &first_a * &second_b - &first_b * &second_a;
            (
                [
                    gram.bilinear(&edge_01, &edge_01),
                    gram.bilinear(&edge_12, &edge_12),
                    gram.bilinear(&edge_20, &edge_20),
                ],
                ExactExpr::from(area_numerator.clone()).divide(ExactExpr::sqrt_int(12)),
                sign(&area_numerator),
            )
        } else {
            let rational = points
                .iter()
                .map(|point| {
                    point.rational.clone().ok_or_else(|| {
                        ProjectionError::Singular(
                            "receiver face did not expose rational triangle coordinates".to_owned(),
                        )
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let edge_01 = rational[1].subtract(&rational[0]);
            let edge_12 = rational[2].subtract(&rational[1]);
            let edge_20 = rational[0].subtract(&rational[2]);
            let edge_02 = rational[2].subtract(&rational[0]);
            let area = edge_01.cross(&edge_02);
            (
                [
                    edge_01.norm_squared(),
                    edge_12.norm_squared(),
                    edge_20.norm_squared(),
                ],
                ExactExpr::from(area.clone()),
                sign(&area),
            )
        };

    let reference = side_squared
        .iter()
        .find(|value| !value.is_zero())
        .cloned()
        .ok_or_else(|| {
            ProjectionError::Singular("the projected triangle has no nonzero side".to_owned())
        })?;
    let side_ratios = side_squared.clone().map(|value| value / &reference);
    let gauge_squared = receiver_metric(receiver)?.reference_squared;
    let gauge_normalized_side_squared = side_squared.clone().map(|value| value / &gauge_squared);

    Ok(TriangleFaceSignature {
        entity,
        side_squared,
        side_ratios,
        gauge_normalized_side_squared,
        parity,
        signed_area_witness,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionDiscriminantKind {
    CollinearProjectedSegments,
    EndpointIntersection,
    EqualDepth,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionDiscriminant {
    pub first_entity: EntityId,
    pub first_segment: usize,
    pub second_entity: EntityId,
    pub second_segment: usize,
    pub kind: ProjectionDiscriminantKind,
    pub statement: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Crossing {
    pub first_entity: EntityId,
    pub first_segment: usize,
    pub second_entity: EntityId,
    pub second_segment: usize,
    pub point: RatVec2,
    pub first_depth: Rat,
    pub second_depth: Rat,
    pub over_entity: EntityId,
    pub orientation_sign: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossingAnalysis {
    pub crossings: Vec<Crossing>,
    pub discriminants: Vec<ProjectionDiscriminant>,
    pub exact: bool,
    pub boundary: Option<String>,
}

#[derive(Clone)]
struct ThreadSegment {
    entity: EntityId,
    ordinal: usize,
    segment_count: usize,
    closed: bool,
    source_a: RatVec3,
    source_b: RatVec3,
    screen_a: RatVec2,
    screen_b: RatVec2,
}

pub fn analyze_crossings(
    construction: &Construction,
    receiver: &Receiver,
) -> Result<CrossingAnalysis, ProjectionError> {
    if matches!(receiver.projection, ProjectionLaw::Isometric) {
        return Ok(CrossingAnalysis {
            crossings: Vec::new(),
            discriminants: Vec::new(),
            exact: false,
            boundary: Some(
                "crossing predicates for the radical isometric chart are not yet implemented"
                    .to_owned(),
            ),
        });
    }

    let mut segments = Vec::new();
    for (entity_id, entity) in &construction.entities {
        let Geometry::Thread { vertices, closed } = &entity.geometry else {
            continue;
        };
        if vertices.len() < 2 {
            continue;
        }
        let segment_count = if *closed {
            vertices.len()
        } else {
            vertices.len() - 1
        };
        for ordinal in 0..segment_count {
            let next = (ordinal + 1) % vertices.len();
            let a = project_point(construction, entity.frame, &vertices[ordinal], receiver)?;
            let b = project_point(construction, entity.frame, &vertices[next], receiver)?;
            let (Some(screen_a), Some(screen_b)) = (a.rational, b.rational) else {
                continue;
            };
            segments.push(ThreadSegment {
                entity: *entity_id,
                ordinal,
                segment_count,
                closed: *closed,
                source_a: a.receiver_point,
                source_b: b.receiver_point,
                screen_a,
                screen_b,
            });
        }
    }

    let mut crossings = Vec::new();
    let mut discriminants = Vec::new();
    for first_index in 0..segments.len() {
        for second_index in (first_index + 1)..segments.len() {
            let first = &segments[first_index];
            let second = &segments[second_index];
            if adjacent(first, second) {
                continue;
            }
            classify_pair(
                first,
                second,
                &receiver.projection,
                &mut crossings,
                &mut discriminants,
            );
        }
    }
    Ok(CrossingAnalysis {
        crossings,
        discriminants,
        exact: true,
        boundary: None,
    })
}

fn adjacent(first: &ThreadSegment, second: &ThreadSegment) -> bool {
    if first.entity != second.entity {
        return false;
    }
    if first.ordinal.abs_diff(second.ordinal) == 1 {
        return true;
    }
    first.closed
        && second.closed
        && ((first.ordinal == 0 && second.ordinal + 1 == second.segment_count)
            || (second.ordinal == 0 && first.ordinal + 1 == first.segment_count))
}

fn classify_pair(
    first: &ThreadSegment,
    second: &ThreadSegment,
    projection: &ProjectionLaw,
    crossings: &mut Vec<Crossing>,
    discriminants: &mut Vec<ProjectionDiscriminant>,
) {
    let first_direction = first.screen_b.subtract(&first.screen_a);
    let second_direction = second.screen_b.subtract(&second.screen_a);
    let denominator = first_direction.cross(&second_direction);
    let offset = second.screen_a.subtract(&first.screen_a);

    if denominator.is_zero() {
        if offset.cross(&first_direction).is_zero() {
            discriminants.push(ProjectionDiscriminant {
                first_entity: first.entity,
                first_segment: first.ordinal,
                second_entity: second.entity,
                second_segment: second.ordinal,
                kind: ProjectionDiscriminantKind::CollinearProjectedSegments,
                statement: "two distinct embedded segments occupy one projected line".to_owned(),
            });
        }
        return;
    }

    let first_screen_parameter = offset.cross(&second_direction) / &denominator;
    let second_screen_parameter = offset.cross(&first_direction) / &denominator;
    if first_screen_parameter.is_negative()
        || first_screen_parameter > Rat::one()
        || second_screen_parameter.is_negative()
        || second_screen_parameter > Rat::one()
    {
        return;
    }

    let point = first
        .screen_a
        .add(&first_direction.scale(&first_screen_parameter));
    let endpoint = first_screen_parameter.is_zero()
        || first_screen_parameter.is_one()
        || second_screen_parameter.is_zero()
        || second_screen_parameter.is_one();
    if endpoint {
        discriminants.push(ProjectionDiscriminant {
            first_entity: first.entity,
            first_segment: first.ordinal,
            second_entity: second.entity,
            second_segment: second.ordinal,
            kind: ProjectionDiscriminantKind::EndpointIntersection,
            statement: "a projected crossing reaches a segment endpoint".to_owned(),
        });
        return;
    }

    let Some(first_parameter) = source_parameter(first, &point, projection) else {
        return;
    };
    let Some(second_parameter) = source_parameter(second, &point, projection) else {
        return;
    };
    let first_source = interpolate(&first.source_a, &first.source_b, &first_parameter);
    let second_source = interpolate(&second.source_a, &second.source_b, &second_parameter);
    let first_depth = depth(first_source, projection);
    let second_depth = depth(second_source, projection);
    if first_depth == second_depth {
        discriminants.push(ProjectionDiscriminant {
            first_entity: first.entity,
            first_segment: first.ordinal,
            second_entity: second.entity,
            second_segment: second.ordinal,
            kind: ProjectionDiscriminantKind::EqualDepth,
            statement: "the receiver cannot order the two projected branches by depth".to_owned(),
        });
        return;
    }

    let first_is_over = first_depth < second_depth;
    let orientation = if first_is_over {
        sign(&first_direction.cross(&second_direction))
    } else {
        sign(&second_direction.cross(&first_direction))
    };
    crossings.push(Crossing {
        first_entity: first.entity,
        first_segment: first.ordinal,
        second_entity: second.entity,
        second_segment: second.ordinal,
        point,
        first_depth,
        second_depth,
        over_entity: if first_is_over {
            first.entity
        } else {
            second.entity
        },
        orientation_sign: orientation,
    });
}

fn source_parameter(
    segment: &ThreadSegment,
    screen_point: &RatVec2,
    projection: &ProjectionLaw,
) -> Option<Rat> {
    let delta = segment.source_b.subtract(&segment.source_a);
    match projection {
        ProjectionLaw::Orthographic => solve_linear_parameter(
            &segment.source_a.x,
            &delta.x,
            &screen_point.x,
            &segment.source_a.y,
            &delta.y,
            &screen_point.y,
        ),
        ProjectionLaw::PerspectiveRay { focal_distance } => {
            let x_denominator = focal_distance * &delta.x - &screen_point.x * &delta.z;
            if !x_denominator.is_zero() {
                return Some(
                    (&screen_point.x * (focal_distance + &segment.source_a.z)
                        - focal_distance * &segment.source_a.x)
                        / x_denominator,
                );
            }
            let y_denominator = focal_distance * &delta.y - &screen_point.y * &delta.z;
            if y_denominator.is_zero() {
                None
            } else {
                Some(
                    (&screen_point.y * (focal_distance + &segment.source_a.z)
                        - focal_distance * &segment.source_a.y)
                        / y_denominator,
                )
            }
        }
        ProjectionLaw::StereographicNorth => {
            let x_denominator = &delta.x + &screen_point.x * &delta.z;
            if !x_denominator.is_zero() {
                return Some(
                    (&screen_point.x * (Rat::one() - &segment.source_a.z) - &segment.source_a.x)
                        / x_denominator,
                );
            }
            let y_denominator = &delta.y + &screen_point.y * &delta.z;
            if y_denominator.is_zero() {
                None
            } else {
                Some(
                    (&screen_point.y * (Rat::one() - &segment.source_a.z) - &segment.source_a.y)
                        / y_denominator,
                )
            }
        }
        ProjectionLaw::Isometric => None,
    }
}

fn solve_linear_parameter(
    first_origin: &Rat,
    first_delta: &Rat,
    first_target: &Rat,
    second_origin: &Rat,
    second_delta: &Rat,
    second_target: &Rat,
) -> Option<Rat> {
    if !first_delta.is_zero() {
        Some((first_target - first_origin) / first_delta)
    } else if !second_delta.is_zero() {
        Some((second_target - second_origin) / second_delta)
    } else {
        None
    }
}

fn interpolate(a: &RatVec3, b: &RatVec3, parameter: &Rat) -> RatVec3 {
    a.add(&b.subtract(a).scale(parameter))
}

fn depth(point: RatVec3, projection: &ProjectionLaw) -> Rat {
    match projection {
        ProjectionLaw::Orthographic | ProjectionLaw::Isometric => point.z,
        ProjectionLaw::PerspectiveRay { focal_distance } => focal_distance + point.z,
        ProjectionLaw::StereographicNorth => Rat::one() - point.z,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::{RatVec3, rat};
    use crate::model::{Construction, Geometry};

    #[test]
    fn exact_spin_composes_projective_cayley_ratios_in_causal_order() {
        let one_sixteenth = ProjectiveRatio::from_rat(&rat(1, 16));
        let composed = one_sixteenth.compose_same_axis(&one_sixteenth);
        assert_eq!(composed.finite(), Some(rat(32, 255)));
        assert_ne!(composed.finite(), Some(rat(1, 8)));

        let step = ExactSpin::axis(ReceiverRotationAxis::X, &one_sixteenth);
        assert_eq!(
            ExactSpin::identity().followed_by(&step).followed_by(&step),
            ExactSpin::axis(ReceiverRotationAxis::X, &composed)
        );
    }

    #[test]
    fn exact_spin_admits_the_cayley_half_turn_and_inverse() {
        let half_turn = ExactSpin::axis(ReceiverRotationAxis::Y, &ProjectiveRatio::infinity());
        assert_eq!(
            half_turn.matrix(),
            RatMat3::from_i64([[-1, 0, 0], [0, 1, 0], [0, 0, -1]])
        );
        assert_eq!(
            half_turn.followed_by(&half_turn.inverse()),
            ExactSpin::identity()
        );
    }

    #[test]
    fn exact_spin_does_not_commute_away_a_traversal_word() {
        let x = ExactSpin::axis(
            ReceiverRotationAxis::X,
            &ProjectiveRatio::from_rat(&rat(1, 3)),
        );
        let y = ExactSpin::axis(
            ReceiverRotationAxis::Y,
            &ProjectiveRatio::from_rat(&rat(1, 5)),
        );
        let xyx = ExactSpin::identity()
            .followed_by(&x)
            .followed_by(&y)
            .followed_by(&x);
        let xxy = ExactSpin::identity()
            .followed_by(&x)
            .followed_by(&x)
            .followed_by(&y);
        assert_ne!(xyx, xxy);
        assert_ne!(xyx.matrix(), xxy.matrix());
    }

    #[test]
    fn exact_spin_binary_power_retains_a_repeated_elementary_word() {
        let step = ExactSpin::axis(
            ReceiverRotationAxis::Z,
            &ProjectiveRatio::new(BigInt::from(1), BigInt::from(16)).unwrap(),
        );
        let repeated = (0..37).fold(ExactSpin::identity(), |product, _| {
            product.followed_by(&step)
        });
        assert_eq!(step.pow(&BigUint::from(37_u8)), repeated);
        assert_eq!(step.pow(&BigUint::zero()), ExactSpin::identity());
    }

    #[test]
    fn isometric_projection_declares_its_exact_compression_fiber() {
        let point = RatVec3::from_i64(1, 2, 3);
        let projected = project_receiver_point(&point, &ProjectionLaw::Isometric).unwrap();
        assert!(projected.rational.is_none());
        assert_eq!(
            ProjectionLaw::Isometric.fiber_statement(),
            "linear fiber span{(1,1,1)}; every source axis has squared scale 2/3"
        );

        let shifted = point.add(&RatVec3::from_i64(5, 5, 5));
        let shifted_projection =
            project_receiver_point(&shifted, &ProjectionLaw::Isometric).unwrap();
        assert_eq!(projected.exact, shifted_projection.exact);

        let (construction, frame) = Construction::new("chart");
        let receiver = Receiver::new(ReceiverId(1), "iso", frame, ProjectionLaw::Isometric);
        let field = project_chart_field(&construction, frame, &receiver, [0, 1], &Rat::one(), 2, 1)
            .unwrap();
        assert_eq!(field.plane_discriminant, rat(1, 3));
        assert!(field.conformal_scale.is_none());
    }

    #[test]
    fn receiver_precession_changes_the_face_not_the_construction() {
        let (mut construction, frame) = Construction::new("body");
        let entity = construction
            .add_entity(
                "thread",
                frame,
                Geometry::Thread {
                    vertices: vec![RatVec3::from_i64(-1, 0, 0), RatVec3::from_i64(1, 0, 1)],
                    closed: false,
                },
            )
            .unwrap();
        let before = construction.clone();
        let receiver_a = Receiver::new(ReceiverId(1), "a", frame, ProjectionLaw::Orthographic);
        let mut receiver_b = receiver_a.clone();
        receiver_b
            .orientation
            .precess_cayley(ReceiverRotationAxis::Y, &rat(1, 2));
        let face_a = project_entity(&construction, entity, &receiver_a, 8).unwrap();
        let face_b = project_entity(&construction, entity, &receiver_b, 8).unwrap();
        assert_ne!(face_a, face_b);
        assert_eq!(construction, before);
    }

    #[test]
    fn receiver_gauge_normalizes_only_its_declared_reference() {
        let (_construction, frame) = Construction::new("body");
        let mut receiver =
            Receiver::new(ReceiverId(1), "gauge", frame, ProjectionLaw::Orthographic);
        receiver
            .orientation
            .precess_cayley(ReceiverRotationAxis::X, &rat(1, 3));
        receiver.gauge.anchor = RatVec3::from_i64(2, -1, 3);
        receiver.gauge.reference = RatVec3::from_i64(1, 1, 0);
        let metric = receiver_metric(&receiver).unwrap();
        assert_eq!(
            metric
                .normalized
                .bilinear(&receiver.gauge.reference, &receiver.gauge.reference),
            Rat::one()
        );
        assert_ne!(
            metric
                .normalized
                .bilinear(&RatVec3::from_i64(1, 0, 0), &RatVec3::from_i64(1, 0, 0)),
            Rat::one()
        );
    }

    #[test]
    fn a_hinged_frame_carries_its_grid_through_the_declared_relation() {
        let (mut construction, frame) = Construction::new("parent");
        let triangle = construction
            .add_entity(
                "triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(0, 0, 0),
                        RatVec3::from_i64(1, 0, 0),
                        RatVec3::from_i64(0, 1, 0),
                    ],
                },
            )
            .unwrap();
        let hinge = construction
            .found_hinge(
                triangle,
                frame,
                RatVec3::zero(),
                crate::model::HingeAxis::X,
                Rat::zero(),
            )
            .unwrap();
        let child = construction.entities[&triangle].frame;
        let receiver = Receiver::new(ReceiverId(1), "parent", frame, ProjectionLaw::Orthographic);
        let before =
            project_chart_field(&construction, child, &receiver, [0, 1], &Rat::one(), 2, 1)
                .unwrap();
        construction.set_hinge_parameter(hinge, rat(1, 2)).unwrap();
        let after = project_chart_field(&construction, child, &receiver, [0, 1], &Rat::one(), 2, 1)
            .unwrap();
        assert_ne!(before.lines, after.lines);
        assert_eq!(before.intrinsic_gram, after.intrinsic_gram);
        assert_eq!(before.intrinsic_orientation, after.intrinsic_orientation);
    }

    #[test]
    fn triangle_similarity_and_parity_are_receiver_face_statements() {
        let (mut construction, frame) = Construction::new("body");
        let triangle = construction
            .add_entity(
                "skew triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(0, 0, 0),
                        RatVec3::from_i64(2, 0, 1),
                        RatVec3::from_i64(0, 1, 2),
                    ],
                },
            )
            .unwrap();
        let first = Receiver::new(ReceiverId(1), "first", frame, ProjectionLaw::Orthographic);
        let mut second = first.clone();
        second.id = ReceiverId(2);
        second
            .orientation
            .precess_cayley(ReceiverRotationAxis::Y, &rat(2, 1));
        let first_signature = triangle_face_signature(&construction, triangle, &first).unwrap();
        let second_signature = triangle_face_signature(&construction, triangle, &second).unwrap();
        assert_ne!(first_signature.side_ratios, second_signature.side_ratios);
        assert_ne!(
            first_signature.signed_area_witness,
            second_signature.signed_area_witness
        );
        assert_ne!(first_signature.parity, second_signature.parity);
        assert_eq!(
            construction.entities[&triangle].geometry.kind_label(),
            "triangle"
        );
    }

    #[test]
    fn a_crossing_face_changes_through_an_exact_projection_discriminant() {
        let (mut construction, frame) = Construction::new("two embedded arcs");
        construction
            .add_entity(
                "horizontal",
                frame,
                Geometry::Thread {
                    vertices: vec![RatVec3::from_i64(-1, 0, 0), RatVec3::from_i64(1, 0, 0)],
                    closed: false,
                },
            )
            .unwrap();
        construction
            .add_entity(
                "transverse",
                frame,
                Geometry::Thread {
                    vertices: vec![
                        RatVec3::new(Rat::zero(), rat(-1, 1), rat(3, 4)),
                        RatVec3::new(Rat::zero(), rat(1, 1), rat(3, 4)),
                    ],
                    closed: false,
                },
            )
            .unwrap();
        let before_construction = construction.clone();
        let mut receiver = Receiver::new(
            ReceiverId(1),
            "precessing",
            frame,
            ProjectionLaw::Orthographic,
        );

        let before = analyze_crossings(&construction, &receiver).unwrap();
        assert_eq!(before.crossings.len(), 1);
        assert!(before.discriminants.is_empty());

        receiver
            .orientation
            .precess_cayley(ReceiverRotationAxis::Y, &rat(1, 2));
        let boundary = analyze_crossings(&construction, &receiver).unwrap();
        assert!(boundary.crossings.is_empty());
        assert_eq!(boundary.discriminants.len(), 1);
        assert_eq!(
            boundary.discriminants[0].kind,
            ProjectionDiscriminantKind::EndpointIntersection
        );

        receiver.orientation = ReceiverOrientation::identity();
        receiver
            .orientation
            .precess_cayley(ReceiverRotationAxis::Y, &rat(2, 3));
        let after = analyze_crossings(&construction, &receiver).unwrap();
        assert!(after.crossings.is_empty());
        assert!(after.discriminants.is_empty());
        assert_eq!(construction, before_construction);
    }
}
