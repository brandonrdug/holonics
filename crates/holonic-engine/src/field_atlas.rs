//! Growing exact local-field standing and receiver-relative restriction.
//!
//! The atlas has no authored population ceiling. Oriented observations refine
//! exact coefficient fibers; an obstruction founds a causally descended germ
//! instead of truncating, averaging, or replacing the prior testimony.
//! Complete images remain receiver sections. Their sample addresses are never
//! promoted into world vertices.
//!
//! It has no authored *dimension* either, and until 2026-08-09 it did: two
//! `const`s named as coefficient counts — `10` and `4` — pinned the ambient
//! dimension at three directly beneath the sentence above. Every coefficient
//! population is now read off a [`FieldChart`] the caller declares per region:
//! `C(n+2,2)` quadric coefficients, `n+1` affine coefficients, `n-1` tangents
//! of a normal. The ceiling that remains is the sample carrier's own —
//! [`RatVec3`] has three coordinates and [`ExactQuadric3`] holds ten — so a
//! chart names between one and three of them, and a chart of dimension `n < 3`
//! resolves in its own coefficient population and lifts into the ambient
//! carrier as the cylinder over its quadric.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, RatVec3, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalDiagram, DiagramError, EventId, EventSuccessor, ExactAffineVersionFiber, ExactEventLaw,
    ExactQuadric3, ExactRaster, ExactTorus, ImageExtent, ImplicitCellId, ImplicitError,
    InverseTransportError, LogicalResourceReceipt, QuadricRayFiber, RayFamily, ReceiverError,
    TorusRayFiber,
};

/// One coordinate of the ambient sample carrier.
///
/// The carrier is [`RatVec3`] and its coordinates are exactly these three, so
/// the ambient dimension is not a level this organ chose: it is the coordinate
/// population of the carrier the samples arrive in. A fourth axis cannot be
/// named here because `RatVec3` has no fourth component.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FieldChartAxis {
    X,
    Y,
    Z,
}

impl FieldChartAxis {
    /// Every coordinate the ambient sample carrier has, in carrier order.
    /// Read off `RatVec3`'s own fields rather than declared here.
    pub const AMBIENT: [Self; 3] = [Self::X, Self::Y, Self::Z];

    pub fn read(self, point: &RatVec3) -> Rat {
        match self {
            Self::X => point.x.clone(),
            Self::Y => point.y.clone(),
            Self::Z => point.z.clone(),
        }
    }

    fn write(self, point: &mut RatVec3, value: Rat) {
        match self {
            Self::X => point.x = value,
            Self::Y => point.y = value,
            Self::Z => point.z = value,
        }
    }
}

/// A degree-at-most-two monomial in a declared chart's coordinates.
///
/// `Cross` always carries its pair in ambient coordinate order, so one
/// monomial has one identity no matter which chart produced it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FieldQuadricMonomial {
    Square(FieldChartAxis),
    Cross(FieldChartAxis, FieldChartAxis),
    Linear(FieldChartAxis),
    Constant,
}

/// The receiver-declared local chart a region's analytical germs are read in.
///
/// The chart is the ordered list of ambient coordinates the region's material
/// is read against. Its dimension `n` fixes every coefficient population this
/// organ needs, and the organ authors none of them:
///
/// ```text
///   quadric coefficients   C(n + 2, 2) = (n + 2)(n + 1) / 2
///   affine coefficients    n + 1
///   tangents of a normal   n - 1
/// ```
///
/// A chart is declared by the caller on the standing before the region founds
/// anything; an undeclared region is read in the ambient chart, which is the
/// carrier's own coordinate population and not a level.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FieldChart {
    axes: Vec<FieldChartAxis>,
}

impl FieldChart {
    pub fn new(axes: Vec<FieldChartAxis>) -> Result<Self, FieldAtlasError> {
        if axes.is_empty() {
            return Err(FieldAtlasError::EmptyChart);
        }
        if axes.iter().copied().collect::<BTreeSet<_>>().len() != axes.len() {
            return Err(FieldAtlasError::RepeatedChartAxis);
        }
        Ok(Self { axes })
    }

    /// Every coordinate the sample carrier has.
    pub fn ambient() -> Self {
        Self {
            axes: FieldChartAxis::AMBIENT.to_vec(),
        }
    }

    pub fn axes(&self) -> &[FieldChartAxis] {
        &self.axes
    }

    pub fn dimension(&self) -> usize {
        self.axes.len()
    }

    pub fn is_ambient(&self) -> bool {
        self.axes == FieldChartAxis::AMBIENT
    }

    /// `C(n + 2, 2)`, the coefficient population of a quadric in `n`
    /// variables.
    pub fn quadric_coefficient_count(&self) -> usize {
        let dimension = self.dimension();
        (dimension + 2) * (dimension + 1) / 2
    }

    /// `n + 1`, the coefficient population of an affine law in `n` variables.
    pub fn affine_coefficient_count(&self) -> usize {
        self.dimension() + 1
    }

    /// The chart's degree-at-most-two monomials in the order the coefficient
    /// fiber's coordinates carry them: squares, crosses, linears, constant.
    /// At the ambient chart this is exactly [`ExactQuadric3`]'s coefficient
    /// order.
    pub fn quadric_monomials(&self) -> Vec<FieldQuadricMonomial> {
        let mut monomials = Vec::with_capacity(self.quadric_coefficient_count());
        monomials.extend(self.axes.iter().map(|axis| FieldQuadricMonomial::Square(*axis)));
        for (position, left) in self.axes.iter().enumerate() {
            for right in &self.axes[position + 1..] {
                monomials.push(FieldQuadricMonomial::Cross(
                    *left.min(right),
                    *left.max(right),
                ));
            }
        }
        monomials.extend(self.axes.iter().map(|axis| FieldQuadricMonomial::Linear(*axis)));
        monomials.push(FieldQuadricMonomial::Constant);
        monomials
    }

    pub fn coordinates(&self, point: &RatVec3) -> Vec<Rat> {
        self.axes.iter().map(|axis| axis.read(point)).collect()
    }

    /// The ambient vector whose chart coordinates are `coordinates` and whose
    /// remaining coordinates are zero.
    pub fn embed(&self, coordinates: &[Rat]) -> RatVec3 {
        let mut point = RatVec3::zero();
        for (axis, coordinate) in self.axes.iter().zip(coordinates) {
            axis.write(&mut point, coordinate.clone());
        }
        point
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FieldRegionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FieldGermId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FieldObservationId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FieldArrowId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FieldOverlapId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ImageSectionId(pub u64);

/// A phase coordinate is meaningful only in its declared receiver or physical
/// basis. RGB channels are receiver coordinates, not universal wavelengths.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FieldPhaseChannel {
    Declared(u64),
    ReceiverCoordinate {
        receiver: ReceiverId,
        coordinate: u8,
    },
}

/// An exact affine law in one declared chart.
///
/// The coefficient population is `n + 1` — one per chart coordinate, then the
/// constant — so the law's own chart states its length rather than a constant
/// stating it for every chart at once.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAffinePhaseLaw {
    chart: FieldChart,
    coefficients: Vec<Rat>,
}

impl ExactAffinePhaseLaw {
    pub fn new(chart: FieldChart, coefficients: Vec<Rat>) -> Result<Self, FieldAtlasError> {
        if coefficients.len() != chart.affine_coefficient_count() {
            return Err(FieldAtlasError::PhaseLawCoefficientPopulation {
                required: chart.affine_coefficient_count(),
                supplied: coefficients.len(),
            });
        }
        Ok(Self {
            chart,
            coefficients,
        })
    }

    pub fn chart(&self) -> &FieldChart {
        &self.chart
    }

    pub fn coefficients(&self) -> &[Rat] {
        &self.coefficients
    }

    pub fn evaluate(&self, point: &RatVec3) -> Rat {
        self.chart
            .coordinates(point)
            .iter()
            .zip(&self.coefficients)
            .fold(Rat::zero(), |total, (coordinate, coefficient)| {
                total + coordinate * coefficient
            })
            + &self.coefficients[self.chart.dimension()]
    }

    /// The ambient gradient. Coordinates outside the chart carry zero, which
    /// is the law's own extension along the directions it does not read.
    pub fn gradient(&self) -> RatVec3 {
        self.chart
            .embed(&self.coefficients[..self.chart.dimension()])
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPhaseFiber {
    pub fiber: ExactAffineVersionFiber,
    pub law: Option<ExactAffinePhaseLaw>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldCoorientation {
    AlongCanonical,
    AgainstCanonical,
}

impl FieldCoorientation {
    fn orient_vector(self, vector: RatVec3) -> RatVec3 {
        match self {
            Self::AlongCanonical => vector,
            Self::AgainstCanonical => vector.scale(&-Rat::one()),
        }
    }

    fn orient_matrix(self, matrix: [[Rat; 3]; 3]) -> [[Rat; 3]; 3] {
        match self {
            Self::AlongCanonical => matrix,
            Self::AgainstCanonical => matrix.map(|row| row.map(|coefficient| -coefficient)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldSupportStanding {
    Quadric {
        implicit: ImplicitCellId,
        fiber: ExactAffineVersionFiber,
        resolved: Option<ExactQuadric3>,
        coorientation: Option<FieldCoorientation>,
    },
    Torus(ExactTorus),
}

impl FieldSupportStanding {
    pub fn implicit_id(&self) -> ImplicitCellId {
        match self {
            Self::Quadric { implicit, .. } => *implicit,
            Self::Torus(torus) => torus.id,
        }
    }

    pub fn is_resolved(&self) -> bool {
        match self {
            Self::Quadric { resolved, .. } => resolved.is_some(),
            Self::Torus(_) => true,
        }
    }

    pub fn gradient(&self, point: &RatVec3) -> Option<RatVec3> {
        match self {
            Self::Quadric {
                resolved: Some(quadric),
                coorientation: Some(coorientation),
                ..
            } => Some(coorientation.orient_vector(quadric.gradient(point))),
            Self::Torus(torus) => Some(torus.gradient(point)),
            Self::Quadric { .. } => None,
        }
    }

    pub fn hessian(&self, point: &RatVec3) -> Option<[[Rat; 3]; 3]> {
        match self {
            Self::Quadric {
                resolved: Some(quadric),
                coorientation: Some(coorientation),
                ..
            } => Some(coorientation.orient_matrix(quadric.hessian())),
            Self::Torus(torus) => Some(torus.hessian(point)),
            Self::Quadric { .. } => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldObstruction {
    pub support: bool,
    pub phase_channels: BTreeSet<FieldPhaseChannel>,
}

impl FieldObstruction {
    fn is_empty(&self) -> bool {
        !self.support && self.phase_channels.is_empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldGermOrigin {
    DerivedFromObservation,
    SourceTorus {
        source_implicit: ImplicitCellId,
    },
    ObstructionEmanation {
        parent: FieldGermId,
        obstruction: FieldObstruction,
    },
}

/// One curvature- and phase-bearing local analytical germ.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalFieldGerm {
    pub id: FieldGermId,
    pub region: FieldRegionId,
    /// The chart this germ was founded in. It is its region's declared chart
    /// at founding, and a region may not redeclare after founding.
    #[serde(default = "FieldChart::ambient")]
    pub chart: FieldChart,
    pub source_event: EventId,
    pub last_event: EventId,
    pub origin: FieldGermOrigin,
    pub parents: BTreeSet<FieldGermId>,
    pub observations: BTreeSet<FieldObservationId>,
    pub lineage: BTreeSet<EventId>,
    pub support: FieldSupportStanding,
    pub phases: BTreeMap<FieldPhaseChannel, ExactPhaseFiber>,
}

impl CausalFieldGerm {
    pub fn resolved_phase_laws(&self) -> BTreeMap<FieldPhaseChannel, ExactAffinePhaseLaw> {
        self.phases
            .iter()
            .filter_map(|(channel, phase)| phase.law.clone().map(|law| (*channel, law)))
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverSampleContact {
    pub receiver: ReceiverId,
    pub column: u32,
    pub row: u32,
}

/// Exact oriented source testimony. Region membership is lawful source
/// identity; the source does not provide an implicit successor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrientedFieldSample {
    pub regions: BTreeSet<FieldRegionId>,
    pub point: RatVec3,
    /// Nonzero, not necessarily normalized.
    pub normal: RatVec3,
    pub phase: BTreeMap<FieldPhaseChannel, Rat>,
    pub receiver_contact: Option<ReceiverSampleContact>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldObservation {
    pub id: FieldObservationId,
    pub event: EventId,
    pub chronology: u64,
    pub regions: BTreeSet<FieldRegionId>,
    pub point: RatVec3,
    pub normal: RatVec3,
    pub phase: BTreeMap<FieldPhaseChannel, Rat>,
    pub receiver_contact: Option<ReceiverSampleContact>,
}

/// A complete finite sensor occurrence. It remains one receiver section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverImageOccurrence {
    pub receiver: ReceiverId,
    pub rays: RayFamily,
    pub raster: ExactRaster,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverImageSection {
    pub id: ImageSectionId,
    pub event: EventId,
    pub chronology: u64,
    pub receiver: ReceiverId,
    pub rays: RayFamily,
    pub raster: ExactRaster,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImageSampleDeparture {
    pub column: u32,
    pub row: u32,
    pub channels: [i16; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImageSectionComparison {
    CommonAperture {
        departures: Vec<ImageSampleDeparture>,
    },
    ChangedAperture {
        previous: ImageExtent,
        current: ImageExtent,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverImageDifference {
    pub receiver: ReceiverId,
    pub previous: ImageSectionId,
    pub current: ImageSectionId,
    pub comparison: ImageSectionComparison,
}

/// Source-declared exact support. Its provenance remains distinguishable from
/// an observation-derived coefficient fiber.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceTorusOccurrence {
    pub region: FieldRegionId,
    pub torus: ExactTorus,
    pub phases: BTreeMap<FieldPhaseChannel, ExactAffinePhaseLaw>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldCausalArrow {
    pub id: FieldArrowId,
    pub event: EventId,
    pub source: FieldGermId,
    pub target: FieldGermId,
    pub obstruction: FieldObstruction,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldOverlapOutcome {
    Glued,
    Open,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldOverlap {
    pub id: FieldOverlapId,
    pub event: EventId,
    pub observation: FieldObservationId,
    pub germs: [FieldGermId; 2],
    pub outcome: FieldOverlapOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalFieldStanding {
    pub schema: String,
    pub used_events: BTreeSet<EventId>,
    pub last_chronology: Option<u64>,
    pub germs: BTreeMap<FieldGermId, CausalFieldGerm>,
    /// Every contemporary alternative per local region. Departed predecessors
    /// remain in `germs` as causal history, not current support.
    pub active_regions: BTreeMap<FieldRegionId, BTreeSet<FieldGermId>>,
    /// The caller's declared chart per region. An absent region is read in the
    /// ambient chart.
    #[serde(default)]
    pub region_charts: BTreeMap<FieldRegionId, FieldChart>,
    pub observations: BTreeMap<FieldObservationId, FieldObservation>,
    pub arrows: BTreeMap<FieldArrowId, FieldCausalArrow>,
    pub overlaps: BTreeMap<FieldOverlapId, FieldOverlap>,
    pub images: BTreeMap<ImageSectionId, ReceiverImageSection>,
    pub image_differences: Vec<ReceiverImageDifference>,
    pub latest_images: BTreeMap<ReceiverId, ImageSectionId>,
    next_germ: u64,
    next_observation: u64,
    next_arrow: u64,
    next_overlap: u64,
    next_image: u64,
    next_implicit: u64,
}

impl Default for CausalFieldStanding {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.causal-field-standing.v1".to_owned(),
            used_events: BTreeSet::new(),
            last_chronology: None,
            germs: BTreeMap::new(),
            active_regions: BTreeMap::new(),
            region_charts: BTreeMap::new(),
            observations: BTreeMap::new(),
            arrows: BTreeMap::new(),
            overlaps: BTreeMap::new(),
            images: BTreeMap::new(),
            image_differences: Vec::new(),
            latest_images: BTreeMap::new(),
            next_germ: 1,
            next_observation: 1,
            next_arrow: 1,
            next_overlap: 1,
            next_image: 1,
            next_implicit: 1,
        }
    }
}

impl CausalFieldStanding {
    /// Declare the chart a region's germs are read in.
    ///
    /// A region that has already founded a germ may not be redeclared: the
    /// germs already carry the chart they were founded in, and a later
    /// declaration would leave the standing describing two charts at once.
    pub fn declare_region_chart(
        &mut self,
        region: FieldRegionId,
        chart: FieldChart,
    ) -> Result<(), FieldAtlasError> {
        if self.germs.values().any(|germ| germ.region == region) {
            return Err(FieldAtlasError::RegionChartAfterFounding(region));
        }
        self.region_charts.insert(region, chart);
        Ok(())
    }

    /// The chart a region is read in. An undeclared region is read in the
    /// ambient chart, which is the sample carrier's coordinate population.
    pub fn region_chart(&self, region: FieldRegionId) -> FieldChart {
        self.region_charts
            .get(&region)
            .cloned()
            .unwrap_or_else(FieldChart::ambient)
    }

    pub fn active_germs(&self) -> BTreeSet<FieldGermId> {
        self.active_regions
            .values()
            .flat_map(|germs| germs.iter().copied())
            .collect()
    }

    pub fn future_cone(&self, root: FieldGermId) -> Result<BTreeSet<FieldGermId>, FieldAtlasError> {
        self.causal_cone(root, true)
    }

    pub fn past_cone(&self, root: FieldGermId) -> Result<BTreeSet<FieldGermId>, FieldAtlasError> {
        self.causal_cone(root, false)
    }

    fn causal_cone(
        &self,
        root: FieldGermId,
        future: bool,
    ) -> Result<BTreeSet<FieldGermId>, FieldAtlasError> {
        if !self.germs.contains_key(&root) {
            return Err(FieldAtlasError::UnknownGerm(root));
        }
        let mut result = BTreeSet::from([root]);
        let mut frontier = VecDeque::from([root]);
        while let Some(germ) = frontier.pop_front() {
            for arrow in self.arrows.values() {
                let next = if future && arrow.source == germ {
                    Some(arrow.target)
                } else if !future && arrow.target == germ {
                    Some(arrow.source)
                } else {
                    None
                };
                if let Some(next) = next
                    && result.insert(next)
                {
                    frontier.push_back(next);
                }
            }
        }
        Ok(result)
    }

    fn allocate_germ(&mut self) -> Result<FieldGermId, FieldAtlasError> {
        let id = FieldGermId(self.next_germ);
        self.next_germ = self
            .next_germ
            .checked_add(1)
            .ok_or(FieldAtlasError::CarrierOverflow)?;
        Ok(id)
    }

    fn allocate_observation(&mut self) -> Result<FieldObservationId, FieldAtlasError> {
        let id = FieldObservationId(self.next_observation);
        self.next_observation = self
            .next_observation
            .checked_add(1)
            .ok_or(FieldAtlasError::CarrierOverflow)?;
        Ok(id)
    }

    fn allocate_arrow(&mut self) -> Result<FieldArrowId, FieldAtlasError> {
        let id = FieldArrowId(self.next_arrow);
        self.next_arrow = self
            .next_arrow
            .checked_add(1)
            .ok_or(FieldAtlasError::CarrierOverflow)?;
        Ok(id)
    }

    fn allocate_overlap(&mut self) -> Result<FieldOverlapId, FieldAtlasError> {
        let id = FieldOverlapId(self.next_overlap);
        self.next_overlap = self
            .next_overlap
            .checked_add(1)
            .ok_or(FieldAtlasError::CarrierOverflow)?;
        Ok(id)
    }

    fn allocate_image(&mut self) -> Result<ImageSectionId, FieldAtlasError> {
        let id = ImageSectionId(self.next_image);
        self.next_image = self
            .next_image
            .checked_add(1)
            .ok_or(FieldAtlasError::CarrierOverflow)?;
        Ok(id)
    }

    fn allocate_implicit(&mut self) -> Result<ImplicitCellId, FieldAtlasError> {
        while self
            .germs
            .values()
            .any(|germ| germ.support.implicit_id().0 == self.next_implicit)
        {
            self.next_implicit = self
                .next_implicit
                .checked_add(1)
                .ok_or(FieldAtlasError::CarrierOverflow)?;
        }
        let id = ImplicitCellId(self.next_implicit);
        self.next_implicit = self
            .next_implicit
            .checked_add(1)
            .ok_or(FieldAtlasError::CarrierOverflow)?;
        Ok(id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalFieldEvent {
    pub event: EventId,
    pub chronology: u64,
    pub images: Vec<ReceiverImageOccurrence>,
    pub oriented_samples: Vec<OrientedFieldSample>,
    pub source_tori: Vec<SourceTorusOccurrence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalFieldRadiation {
    pub schema: String,
    pub event: EventId,
    pub founded_germs: BTreeSet<FieldGermId>,
    pub refined_germs: BTreeSet<FieldGermId>,
    pub emanations: BTreeSet<FieldArrowId>,
    pub overlaps: BTreeSet<FieldOverlapId>,
    pub image_sections: BTreeSet<ImageSectionId>,
    pub image_differences: Vec<ReceiverImageDifference>,
    pub germ_population_after: u64,
    pub active_population_after: u64,
    pub unresolved_active_after: u64,
}

impl CausalFieldRadiation {
    fn new(event: EventId) -> Self {
        Self {
            schema: "holonic-engine.causal-field-radiation.v1".to_owned(),
            event,
            founded_germs: BTreeSet::new(),
            refined_germs: BTreeSet::new(),
            emanations: BTreeSet::new(),
            overlaps: BTreeSet::new(),
            image_sections: BTreeSet::new(),
            image_differences: Vec::new(),
            germ_population_after: 0,
            active_population_after: 0,
            unresolved_active_after: 0,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct CausalFieldAtlasLaw;

impl CausalFieldAtlasLaw {
    pub fn initial_standing(&self) -> CausalFieldStanding {
        CausalFieldStanding::default()
    }
}

impl ExactEventLaw for CausalFieldAtlasLaw {
    type Standing = CausalFieldStanding;
    type Event = CausalFieldEvent;
    type Radiation = CausalFieldRadiation;
    type Error = FieldAtlasError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        validate_standing(standing_before)?;
        validate_event(standing_before, event)?;

        let mut standing_after = standing_before.clone();
        let mut radiation = CausalFieldRadiation::new(event.event);
        let mut logical = CausalDiagram::default();

        let mut event_images = BTreeMap::new();
        for image in &event.images {
            logical.add_event("receive-image-section");
            let section = admit_image(&mut standing_after, event, image)?;
            event_images.insert(image.receiver, section.id);
            radiation.image_sections.insert(section.id);
            if let Some(difference) = standing_after.image_differences.last()
                && difference.current == section.id
            {
                radiation.image_differences.push(difference.clone());
            }
        }

        for source in &event.source_tori {
            logical.add_event("receive-source-torus");
            let germ = admit_source_torus(&mut standing_after, event, source)?;
            radiation.founded_germs.insert(germ);
        }

        for sample in &event.oriented_samples {
            logical.add_event("admit-oriented-field-sample");
            admit_oriented_sample(
                &mut standing_after,
                event,
                sample,
                &event_images,
                &mut radiation,
            )?;
        }

        standing_after.used_events.insert(event.event);
        standing_after.last_chronology = Some(event.chronology);
        let active = standing_after.active_germs();
        radiation.germ_population_after = usize_to_u64(standing_after.germs.len())?;
        radiation.active_population_after = usize_to_u64(active.len())?;
        radiation.unresolved_active_after = usize_to_u64(
            active
                .iter()
                .filter(|germ| !standing_after.germs[germ].support.is_resolved())
                .count(),
        )?;

        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: Some(LogicalResourceReceipt::from_diagram(&logical)?),
            physical_resources: None,
        })
    }
}

fn validate_standing(standing: &CausalFieldStanding) -> Result<(), FieldAtlasError> {
    if standing.schema != "holonic-engine.causal-field-standing.v1" {
        return Err(FieldAtlasError::MalformedStanding);
    }
    for (region, active) in &standing.active_regions {
        if active.is_empty()
            || active.iter().any(|germ| {
                standing
                    .germs
                    .get(germ)
                    .is_none_or(|germ| germ.region != *region)
            })
        {
            return Err(FieldAtlasError::MalformedStanding);
        }
    }
    if standing
        .germs
        .values()
        .any(|germ| germ.chart != standing.region_chart(germ.region))
    {
        return Err(FieldAtlasError::MalformedStanding);
    }
    if standing.germs.values().any(|germ| {
        matches!(
            &germ.support,
            FieldSupportStanding::Quadric {
                resolved: Some(_),
                coorientation: None,
                ..
            } | FieldSupportStanding::Quadric {
                resolved: None,
                coorientation: Some(_),
                ..
            }
        )
    }) {
        return Err(FieldAtlasError::MalformedStanding);
    }
    Ok(())
}

fn validate_event(
    standing: &CausalFieldStanding,
    event: &CausalFieldEvent,
) -> Result<(), FieldAtlasError> {
    if event.images.is_empty() && event.oriented_samples.is_empty() && event.source_tori.is_empty()
    {
        return Err(FieldAtlasError::EmptyEvent);
    }
    if standing.used_events.contains(&event.event) {
        return Err(FieldAtlasError::RepeatedEvent(event.event));
    }
    if let Some(previous) = standing.last_chronology
        && event.chronology <= previous
    {
        return Err(FieldAtlasError::NoncausalChronology {
            previous,
            supplied: event.chronology,
        });
    }
    let image_receivers = event
        .images
        .iter()
        .map(|image| image.receiver)
        .collect::<BTreeSet<_>>();
    if image_receivers.len() != event.images.len() {
        return Err(FieldAtlasError::DuplicateImageReceiver);
    }
    for image in &event.images {
        image.rays.validate()?;
    }
    for sample in &event.oriented_samples {
        if sample.regions.is_empty() {
            return Err(FieldAtlasError::EmptySampleRegion);
        }
        if sample.normal == RatVec3::zero() {
            return Err(FieldAtlasError::ZeroSampleNormal);
        }
    }
    Ok(())
}

fn admit_image(
    standing: &mut CausalFieldStanding,
    event: &CausalFieldEvent,
    occurrence: &ReceiverImageOccurrence,
) -> Result<ReceiverImageSection, FieldAtlasError> {
    let id = standing.allocate_image()?;
    let section = ReceiverImageSection {
        id,
        event: event.event,
        chronology: event.chronology,
        receiver: occurrence.receiver,
        rays: occurrence.rays.clone(),
        raster: occurrence.raster.clone(),
    };
    if let Some(previous) = standing.latest_images.get(&occurrence.receiver).copied() {
        let previous_section = standing
            .images
            .get(&previous)
            .ok_or(FieldAtlasError::MalformedStanding)?;
        standing
            .image_differences
            .push(compare_images(previous_section, &section)?);
    }
    standing.images.insert(id, section.clone());
    standing.latest_images.insert(occurrence.receiver, id);
    Ok(section)
}

fn compare_images(
    previous: &ReceiverImageSection,
    current: &ReceiverImageSection,
) -> Result<ReceiverImageDifference, FieldAtlasError> {
    let comparison = if previous.raster.extent != current.raster.extent {
        ImageSectionComparison::ChangedAperture {
            previous: previous.raster.extent,
            current: current.raster.extent,
        }
    } else {
        let mut departures = Vec::new();
        for row in 0..current.raster.extent.height {
            for column in 0..current.raster.extent.width {
                let before = previous
                    .raster
                    .sample(column, row)
                    .ok_or(FieldAtlasError::MalformedImageSection)?;
                let after = current
                    .raster
                    .sample(column, row)
                    .ok_or(FieldAtlasError::MalformedImageSection)?;
                let channels = std::array::from_fn(|channel| {
                    i16::from(after.channels()[channel]) - i16::from(before.channels()[channel])
                });
                if channels != [0, 0, 0] {
                    departures.push(ImageSampleDeparture {
                        column,
                        row,
                        channels,
                    });
                }
            }
        }
        ImageSectionComparison::CommonAperture { departures }
    };
    Ok(ReceiverImageDifference {
        receiver: current.receiver,
        previous: previous.id,
        current: current.id,
        comparison,
    })
}

fn admit_source_torus(
    standing: &mut CausalFieldStanding,
    event: &CausalFieldEvent,
    occurrence: &SourceTorusOccurrence,
) -> Result<FieldGermId, FieldAtlasError> {
    if occurrence.torus.source_event > occurrence.torus.last_event
        || occurrence.torus.last_event > event.event
    {
        return Err(FieldAtlasError::SourceTorusChronology {
            source_event: occurrence.torus.source_event,
            last_event: occurrence.torus.last_event,
            event: event.event,
        });
    }
    if standing
        .germs
        .values()
        .any(|germ| germ.support.implicit_id() == occurrence.torus.id)
    {
        return Err(FieldAtlasError::DuplicateImplicitIdentity(
            occurrence.torus.id,
        ));
    }
    let chart = standing.region_chart(occurrence.region);
    if !chart.is_ambient() {
        // `ExactTorus` carries an ambient center and axis, so a source torus
        // cannot be read in a proper sub-chart of the sample carrier.
        return Err(FieldAtlasError::SourceTorusOutsideAmbientChart {
            region: occurrence.region,
            chart,
        });
    }
    if let Some(law) = occurrence
        .phases
        .values()
        .find(|law| *law.chart() != chart)
    {
        return Err(FieldAtlasError::PhaseLawChartMismatch {
            region: occurrence.region,
            declared: chart,
            supplied: law.chart().clone(),
        });
    }
    let id = standing.allocate_germ()?;
    let mut torus = occurrence.torus.clone();
    torus.last_event = event.event;
    let phases = occurrence
        .phases
        .iter()
        .map(|(channel, law)| Ok((*channel, phase_fiber_from_law(law)?)))
        .collect::<Result<_, FieldAtlasError>>()?;
    standing.germs.insert(
        id,
        CausalFieldGerm {
            id,
            region: occurrence.region,
            chart,
            source_event: event.event,
            last_event: event.event,
            origin: FieldGermOrigin::SourceTorus {
                source_implicit: occurrence.torus.id,
            },
            parents: BTreeSet::new(),
            observations: BTreeSet::new(),
            lineage: BTreeSet::from([event.event]),
            support: FieldSupportStanding::Torus(torus),
            phases,
        },
    );
    standing
        .active_regions
        .entry(occurrence.region)
        .or_default()
        .insert(id);
    standing.next_implicit = standing
        .next_implicit
        .max(occurrence.torus.id.0.saturating_add(1));
    Ok(id)
}

fn admit_oriented_sample(
    standing: &mut CausalFieldStanding,
    event: &CausalFieldEvent,
    sample: &OrientedFieldSample,
    event_images: &BTreeMap<ReceiverId, ImageSectionId>,
    radiation: &mut CausalFieldRadiation,
) -> Result<(), FieldAtlasError> {
    let phase = complete_sample_phase(standing, sample, event_images)?;
    let observation_id = standing.allocate_observation()?;
    let observation = FieldObservation {
        id: observation_id,
        event: event.event,
        chronology: event.chronology,
        regions: sample.regions.clone(),
        point: sample.point.clone(),
        normal: sample.normal.clone(),
        phase,
        receiver_contact: sample.receiver_contact.clone(),
    };
    standing
        .observations
        .insert(observation_id, observation.clone());

    let mut contemporary = BTreeMap::<FieldRegionId, BTreeSet<FieldGermId>>::new();
    for region in &sample.regions {
        let active = standing
            .active_regions
            .get(region)
            .cloned()
            .unwrap_or_default();
        let mut next_active = BTreeSet::new();
        if active.is_empty() {
            let germ = new_quadric_germ(standing, event.event, *region, &observation)?;
            radiation.founded_germs.insert(germ);
            next_active.insert(germ);
        } else {
            for germ_id in active {
                let germ = standing
                    .germs
                    .get(&germ_id)
                    .cloned()
                    .ok_or(FieldAtlasError::MalformedStanding)?;
                match admit_sample_to_germ(germ, &observation, &standing.observations)? {
                    Ok(updated) => {
                        standing.germs.insert(germ_id, updated);
                        radiation.refined_germs.insert(germ_id);
                        next_active.insert(germ_id);
                    }
                    Err(obstruction) => {
                        // The refused continuation remains a contemporary local
                        // alternative. The obstruction founds an additional
                        // causal branch; it does not overwrite the earlier germ.
                        next_active.insert(germ_id);
                        let child = emanate_germ(
                            standing,
                            event.event,
                            *region,
                            germ_id,
                            &obstruction,
                            &observation,
                        )?;
                        let arrow_id = standing.allocate_arrow()?;
                        standing.arrows.insert(
                            arrow_id,
                            FieldCausalArrow {
                                id: arrow_id,
                                event: event.event,
                                source: germ_id,
                                target: child,
                                obstruction,
                            },
                        );
                        radiation.founded_germs.insert(child);
                        radiation.emanations.insert(arrow_id);
                        next_active.insert(child);
                    }
                }
            }
        }
        standing.active_regions.insert(*region, next_active.clone());
        contemporary.insert(*region, next_active);
    }

    let regions = contemporary.keys().copied().collect::<Vec<_>>();
    let mut emitted_pairs = BTreeSet::new();
    for left_index in 0..regions.len() {
        for right_index in (left_index + 1)..regions.len() {
            for left in &contemporary[&regions[left_index]] {
                for right in &contemporary[&regions[right_index]] {
                    let pair = canonical_germ_pair(*left, *right);
                    if !emitted_pairs.insert(pair) {
                        continue;
                    }
                    let outcome = overlap_outcome(
                        &standing.germs[&pair[0]],
                        &standing.germs[&pair[1]],
                        &observation.point,
                    );
                    let id = standing.allocate_overlap()?;
                    standing.overlaps.insert(
                        id,
                        FieldOverlap {
                            id,
                            event: event.event,
                            observation: observation_id,
                            germs: pair,
                            outcome,
                        },
                    );
                    radiation.overlaps.insert(id);
                }
            }
        }
    }
    Ok(())
}

fn complete_sample_phase(
    standing: &CausalFieldStanding,
    sample: &OrientedFieldSample,
    event_images: &BTreeMap<ReceiverId, ImageSectionId>,
) -> Result<BTreeMap<FieldPhaseChannel, Rat>, FieldAtlasError> {
    let mut phase = sample.phase.clone();
    let Some(contact) = &sample.receiver_contact else {
        return Ok(phase);
    };
    let section_id = event_images
        .get(&contact.receiver)
        .copied()
        .or_else(|| standing.latest_images.get(&contact.receiver).copied())
        .ok_or(FieldAtlasError::MissingContactImage(contact.receiver))?;
    let section = standing
        .images
        .get(&section_id)
        .ok_or(FieldAtlasError::MalformedStanding)?;
    let sample_rgb = section.raster.sample(contact.column, contact.row).ok_or(
        FieldAtlasError::ImageContactOutsideAperture {
            receiver: contact.receiver,
            column: contact.column,
            row: contact.row,
        },
    )?;
    for (coordinate, value) in sample_rgb.channels().into_iter().enumerate() {
        let channel = FieldPhaseChannel::ReceiverCoordinate {
            receiver: contact.receiver,
            coordinate: u8::try_from(coordinate).map_err(|_| FieldAtlasError::CarrierOverflow)?,
        };
        let value = Rat::from_integer(i64::from(value).into());
        if let Some(existing) = phase.insert(channel, value.clone())
            && existing != value
        {
            return Err(FieldAtlasError::ConflictingContactPhase(channel));
        }
    }
    Ok(phase)
}

fn new_quadric_germ(
    standing: &mut CausalFieldStanding,
    event: EventId,
    region: FieldRegionId,
    observation: &FieldObservation,
) -> Result<FieldGermId, FieldAtlasError> {
    let chart = standing.region_chart(region);
    let id = standing.allocate_germ()?;
    let implicit = standing.allocate_implicit()?;
    let germ = CausalFieldGerm {
        id,
        region,
        source_event: event,
        last_event: event,
        origin: FieldGermOrigin::DerivedFromObservation,
        parents: BTreeSet::new(),
        observations: BTreeSet::new(),
        lineage: BTreeSet::new(),
        support: FieldSupportStanding::Quadric {
            implicit,
            fiber: ExactAffineVersionFiber::new(chart.quadric_coefficient_count())?,
            resolved: None,
            coorientation: None,
        },
        chart,
        phases: BTreeMap::new(),
    };
    let admitted = admit_sample_to_germ(germ, observation, &standing.observations)?
        .map_err(|_| FieldAtlasError::FreshGermObstructed)?;
    standing.germs.insert(id, admitted);
    Ok(id)
}

fn emanate_germ(
    standing: &mut CausalFieldStanding,
    event: EventId,
    region: FieldRegionId,
    parent: FieldGermId,
    obstruction: &FieldObstruction,
    observation: &FieldObservation,
) -> Result<FieldGermId, FieldAtlasError> {
    let parent_germ = standing
        .germs
        .get(&parent)
        .cloned()
        .ok_or(FieldAtlasError::MalformedStanding)?;
    let id = standing.allocate_germ()?;
    let chart = parent_germ.chart.clone();
    let support = if obstruction.support {
        FieldSupportStanding::Quadric {
            implicit: standing.allocate_implicit()?,
            fiber: ExactAffineVersionFiber::new(chart.quadric_coefficient_count())?,
            resolved: None,
            coorientation: None,
        }
    } else {
        clone_support_for_emanation(standing.allocate_implicit()?, event, &parent_germ.support)?
    };
    let germ = CausalFieldGerm {
        id,
        region,
        chart,
        source_event: event,
        last_event: event,
        origin: FieldGermOrigin::ObstructionEmanation {
            parent,
            obstruction: obstruction.clone(),
        },
        parents: BTreeSet::from([parent]),
        observations: BTreeSet::new(),
        lineage: parent_germ.lineage.iter().copied().chain([event]).collect(),
        support,
        phases: parent_germ
            .phases
            .into_iter()
            .filter(|(channel, _)| !obstruction.phase_channels.contains(channel))
            .collect(),
    };
    let admitted = admit_sample_to_germ(germ, observation, &standing.observations)?
        .map_err(|_| FieldAtlasError::FreshGermObstructed)?;
    standing.germs.insert(id, admitted);
    Ok(id)
}

fn clone_support_for_emanation(
    implicit: ImplicitCellId,
    event: EventId,
    support: &FieldSupportStanding,
) -> Result<FieldSupportStanding, FieldAtlasError> {
    Ok(match support {
        FieldSupportStanding::Quadric {
            fiber,
            resolved,
            coorientation,
            ..
        } => FieldSupportStanding::Quadric {
            implicit,
            fiber: fiber.clone(),
            resolved: resolved
                .as_ref()
                .map(|quadric| {
                    let mut quadric =
                        ExactQuadric3::new(implicit, event, quadric.coefficients.clone())?;
                    quadric.last_event = event;
                    Ok::<ExactQuadric3, FieldAtlasError>(quadric)
                })
                .transpose()?,
            coorientation: *coorientation,
        },
        FieldSupportStanding::Torus(torus) => {
            let mut torus = ExactTorus::new(
                implicit,
                event,
                torus.center.clone(),
                torus.axis.clone(),
                torus.major_radius.clone(),
                torus.minor_radius.clone(),
            )?;
            torus.last_event = event;
            FieldSupportStanding::Torus(torus)
        }
    })
}

fn admit_sample_to_germ(
    mut germ: CausalFieldGerm,
    observation: &FieldObservation,
    observations: &BTreeMap<FieldObservationId, FieldObservation>,
) -> Result<Result<CausalFieldGerm, FieldObstruction>, FieldAtlasError> {
    let mut obstruction = FieldObstruction {
        support: false,
        phase_channels: BTreeSet::new(),
    };
    let chart = germ.chart.clone();
    match &mut germ.support {
        FieldSupportStanding::Quadric {
            implicit,
            fiber,
            resolved,
            coorientation,
        } => {
            let mut trial = fiber.clone();
            for coefficients in
                quadric_observation_rows(&chart, &observation.point, &observation.normal)?
            {
                trial.admit(coefficients, Rat::zero())?;
                if trial.affine_dimension() == 0 {
                    obstruction.support = true;
                    break;
                }
            }
            if !obstruction.support {
                let candidate = resolve_quadric(
                    &chart,
                    *implicit,
                    germ.source_event,
                    observation.event,
                    &trial,
                )?;
                let candidate_coorientation = candidate
                    .as_ref()
                    .map(|quadric| {
                        resolve_quadric_coorientation(
                            quadric,
                            &germ.observations,
                            observation,
                            observations,
                        )
                    })
                    .transpose()?
                    .flatten();
                if candidate.is_some() && candidate_coorientation.is_none() {
                    obstruction.support = true;
                } else {
                    *fiber = trial;
                    *resolved = candidate;
                    *coorientation = candidate_coorientation;
                }
            }
        }
        FieldSupportStanding::Torus(torus) => {
            let gradient = torus.gradient(&observation.point);
            if torus.evaluate(&observation.point) != Rat::zero()
                || gradient == RatVec3::zero()
                || gradient.cross(&observation.normal) != RatVec3::zero()
                || !gradient.dot(&observation.normal).is_positive()
            {
                obstruction.support = true;
            }
        }
    }

    let mut phases = germ.phases.clone();
    for (channel, value) in &observation.phase {
        let phase = phases.entry(*channel).or_insert(ExactPhaseFiber {
            fiber: ExactAffineVersionFiber::new(chart.affine_coefficient_count())?,
            law: None,
        });
        match phase
            .fiber
            .admit(affine_point_row(&chart, &observation.point), value.clone())
        {
            Ok(_) => {
                phase.law = resolve_phase_law(&chart, &phase.fiber)?;
            }
            Err(InverseTransportError::AffineFiberObstructed) => {
                obstruction.phase_channels.insert(*channel);
            }
            Err(error) => return Err(error.into()),
        }
    }
    if !obstruction.is_empty() {
        return Ok(Err(obstruction));
    }

    germ.last_event = observation.event;
    germ.observations.insert(observation.id);
    germ.lineage.insert(observation.event);
    germ.phases = phases;
    match &mut germ.support {
        FieldSupportStanding::Quadric {
            resolved: Some(quadric),
            ..
        } => quadric.last_event = observation.event,
        FieldSupportStanding::Torus(torus) => torus.last_event = observation.event,
        FieldSupportStanding::Quadric { resolved: None, .. } => {}
    }
    Ok(Ok(germ))
}

fn resolve_quadric_coorientation(
    quadric: &ExactQuadric3,
    prior: &BTreeSet<FieldObservationId>,
    current: &FieldObservation,
    observations: &BTreeMap<FieldObservationId, FieldObservation>,
) -> Result<Option<FieldCoorientation>, FieldAtlasError> {
    let mut coorientation = None;
    for observation in prior
        .iter()
        .map(|id| {
            observations
                .get(id)
                .ok_or(FieldAtlasError::MalformedStanding)
        })
        .chain([Ok(current)])
    {
        let observation = observation?;
        let gradient = quadric.gradient(&observation.point);
        let alignment = gradient.dot(&observation.normal);
        if quadric.evaluate(&observation.point) != Rat::zero()
            || gradient == RatVec3::zero()
            || gradient.cross(&observation.normal) != RatVec3::zero()
            || alignment.is_zero()
        {
            return Ok(None);
        }
        let observed = if alignment.is_positive() {
            FieldCoorientation::AlongCanonical
        } else {
            FieldCoorientation::AgainstCanonical
        };
        if coorientation.is_some_and(|existing| existing != observed) {
            return Ok(None);
        }
        coorientation = Some(observed);
    }
    Ok(coorientation)
}

fn monomial_value(monomial: FieldQuadricMonomial, point: &RatVec3) -> Rat {
    match monomial {
        FieldQuadricMonomial::Square(axis) => {
            let coordinate = axis.read(point);
            &coordinate * &coordinate
        }
        FieldQuadricMonomial::Cross(left, right) => &left.read(point) * &right.read(point),
        FieldQuadricMonomial::Linear(axis) => axis.read(point),
        FieldQuadricMonomial::Constant => Rat::one(),
    }
}

/// The coefficient of `monomial` in the partial derivative with respect to
/// `direction`.
fn monomial_derivative(
    monomial: FieldQuadricMonomial,
    direction: FieldChartAxis,
    point: &RatVec3,
) -> Rat {
    match monomial {
        FieldQuadricMonomial::Square(axis) if axis == direction => {
            Rat::from_integer(2.into()) * axis.read(point)
        }
        FieldQuadricMonomial::Cross(left, right) if left == direction => right.read(point),
        FieldQuadricMonomial::Cross(left, right) if right == direction => left.read(point),
        FieldQuadricMonomial::Linear(axis) if axis == direction => Rat::one(),
        _ => Rat::zero(),
    }
}

/// One oriented observation as exact rows of the chart's coefficient fiber.
///
/// The population is `1 + (n - 1)`: the value row, and one row per tangent of
/// the chart-projected normal. Nothing here is authored — both counts come
/// from the chart's own coordinate list.
fn quadric_observation_rows(
    chart: &FieldChart,
    point: &RatVec3,
    normal: &RatVec3,
) -> Result<Vec<Vec<Rat>>, FieldAtlasError> {
    let monomials = chart.quadric_monomials();
    let value = monomials
        .iter()
        .map(|monomial| monomial_value(*monomial, point))
        .collect::<Vec<_>>();
    let gradient_rows = chart
        .axes()
        .iter()
        .map(|direction| {
            monomials
                .iter()
                .map(|monomial| monomial_derivative(*monomial, *direction, point))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut rows = vec![value];
    for tangent in chart_tangent_basis(chart, normal)? {
        rows.push(combine_gradient_rows(&gradient_rows, &tangent));
    }
    Ok(rows)
}

/// An exact basis of the chart-orthogonal complement of a normal, in chart
/// coordinates.
///
/// For a normal whose chart coordinates are `v` with `v[p] != 0`, the family
/// `v[p]·e_i - v[i]·e_p` for every `i != p` is orthogonal to `v` and
/// independent, and has exactly `n - 1` members. A normal whose chart
/// projection is zero carries no orientation this chart can read, and is
/// refused rather than projected away.
fn chart_tangent_basis(
    chart: &FieldChart,
    normal: &RatVec3,
) -> Result<Vec<Vec<Rat>>, FieldAtlasError> {
    let coordinates = chart.coordinates(normal);
    let pivot = coordinates
        .iter()
        .position(|coordinate| !coordinate.is_zero())
        .ok_or(FieldAtlasError::SampleNormalOutsideChart {
            chart: chart.clone(),
        })?;
    let mut tangents = Vec::new();
    for index in 0..coordinates.len() {
        if index == pivot {
            continue;
        }
        let mut tangent = vec![Rat::zero(); coordinates.len()];
        tangent[index] = coordinates[pivot].clone();
        tangent[pivot] = -coordinates[index].clone();
        tangents.push(tangent);
    }
    Ok(tangents)
}

fn combine_gradient_rows(gradient_rows: &[Vec<Rat>], direction: &[Rat]) -> Vec<Rat> {
    let mut row = vec![Rat::zero(); gradient_rows.first().map_or(0, Vec::len)];
    for (gradient, weight) in gradient_rows.iter().zip(direction) {
        for (entry, coefficient) in row.iter_mut().zip(gradient) {
            *entry += weight * coefficient;
        }
    }
    row
}

/// Place a chart's quadric coefficients into the ambient support carrier.
///
/// The chart's monomials are a subset of the ambient chart's, so the lift is
/// the inclusion `C(n+2,2) -> C(5,2)` with zero in every ambient monomial the
/// chart does not carry. Geometrically it is the cylinder over the chart's
/// quadric along the coordinates the chart does not read, which contains every
/// ambient point whose chart projection the quadric contains.
fn lift_quadric_to_ambient(
    chart: &FieldChart,
    coefficients: Vec<Rat>,
) -> Result<Vec<Rat>, FieldAtlasError> {
    let ambient = FieldChart::ambient();
    let ambient_monomials = ambient.quadric_monomials();
    let mut lifted = vec![Rat::zero(); ambient.quadric_coefficient_count()];
    for (monomial, coefficient) in chart.quadric_monomials().into_iter().zip(coefficients) {
        let slot = ambient_monomials
            .iter()
            .position(|ambient_monomial| *ambient_monomial == monomial)
            .ok_or(FieldAtlasError::MalformedQuadricFiber)?;
        lifted[slot] = coefficient;
    }
    Ok(lifted)
}

fn resolve_quadric(
    chart: &FieldChart,
    implicit: ImplicitCellId,
    source_event: EventId,
    last_event: EventId,
    fiber: &ExactAffineVersionFiber,
) -> Result<Option<ExactQuadric3>, FieldAtlasError> {
    if fiber.affine_dimension() != 1 {
        return Ok(None);
    }
    let pivots = fiber
        .rows()
        .iter()
        .map(|row| row.pivot)
        .collect::<BTreeSet<_>>();
    let free = (0..chart.quadric_coefficient_count())
        .find(|coordinate| !pivots.contains(coordinate))
        .ok_or(FieldAtlasError::MalformedQuadricFiber)?;
    let mut coefficients = vec![Rat::zero(); chart.quadric_coefficient_count()];
    coefficients[free] = Rat::one();
    for row in fiber.rows() {
        coefficients[row.pivot] = -row.coefficients[free].clone();
    }
    let lifted = lift_quadric_to_ambient(chart, coefficients)?
        .try_into()
        .map_err(|_| FieldAtlasError::MalformedQuadricFiber)?;
    let mut quadric = ExactQuadric3::new(implicit, source_event, lifted)?;
    quadric.last_event = last_event;
    Ok(Some(quadric))
}

fn affine_point_row(chart: &FieldChart, point: &RatVec3) -> Vec<Rat> {
    let mut row = chart.coordinates(point);
    row.push(Rat::one());
    row
}

fn resolve_phase_law(
    chart: &FieldChart,
    fiber: &ExactAffineVersionFiber,
) -> Result<Option<ExactAffinePhaseLaw>, FieldAtlasError> {
    if fiber.variable_count() != chart.affine_coefficient_count() {
        return Err(FieldAtlasError::MalformedPhaseFiber);
    }
    let Some(solution) = fiber.unique_solution()? else {
        return Ok(None);
    };
    Ok(Some(ExactAffinePhaseLaw::new(chart.clone(), solution)?))
}

fn phase_fiber_from_law(law: &ExactAffinePhaseLaw) -> Result<ExactPhaseFiber, FieldAtlasError> {
    let chart = law.chart().clone();
    let mut fiber = ExactAffineVersionFiber::new(chart.affine_coefficient_count())?;
    let mut points = vec![RatVec3::zero()];
    for index in 0..chart.dimension() {
        let mut unit = vec![Rat::zero(); chart.dimension()];
        unit[index] = Rat::one();
        points.push(chart.embed(&unit));
    }
    for point in points {
        fiber.admit(affine_point_row(&chart, &point), law.evaluate(&point))?;
    }
    Ok(ExactPhaseFiber {
        law: resolve_phase_law(&chart, &fiber)?,
        fiber,
    })
}

fn overlap_outcome(
    left: &CausalFieldGerm,
    right: &CausalFieldGerm,
    point: &RatVec3,
) -> FieldOverlapOutcome {
    let admitted = |germ: &CausalFieldGerm| match &germ.support {
        FieldSupportStanding::Quadric {
            resolved: Some(quadric),
            ..
        } => Some(quadric.evaluate(point).is_zero()),
        FieldSupportStanding::Torus(torus) => Some(torus.evaluate(point).is_zero()),
        FieldSupportStanding::Quadric { resolved: None, .. } => None,
    };
    match (admitted(left), admitted(right)) {
        (Some(true), Some(true)) => FieldOverlapOutcome::Glued,
        _ => FieldOverlapOutcome::Open,
    }
}

fn canonical_germ_pair(left: FieldGermId, right: FieldGermId) -> [FieldGermId; 2] {
    if left < right {
        [left, right]
    } else {
        [right, left]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldReceiverQuery {
    pub receiver: ReceiverId,
    pub ray: crate::ExactRay,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldGermTestimony {
    pub germ: FieldGermId,
    pub region: FieldRegionId,
    /// The chart the germ was founded in, so a receipt states the chart its
    /// fibers were read against without consulting the standing.
    #[serde(default = "FieldChart::ambient")]
    pub chart: FieldChart,
    pub source_event: EventId,
    pub last_event: EventId,
    pub origin: FieldGermOrigin,
    pub parents: BTreeSet<FieldGermId>,
    pub lineage: BTreeSet<EventId>,
}

impl From<&CausalFieldGerm> for FieldGermTestimony {
    fn from(germ: &CausalFieldGerm) -> Self {
        Self {
            germ: germ.id,
            region: germ.region,
            chart: germ.chart.clone(),
            source_event: germ.source_event,
            last_event: germ.last_event,
            origin: germ.origin.clone(),
            parents: germ.parents.clone(),
            lineage: germ.lineage.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactFieldRayFiber {
    Quadric {
        testimony: FieldGermTestimony,
        support: ExactQuadric3,
        coorientation: FieldCoorientation,
        fiber: QuadricRayFiber,
        phases: BTreeMap<FieldPhaseChannel, ExactAffinePhaseLaw>,
    },
    Torus {
        testimony: FieldGermTestimony,
        support: ExactTorus,
        fiber: TorusRayFiber,
        phases: BTreeMap<FieldPhaseChannel, ExactAffinePhaseLaw>,
    },
}

impl ExactFieldRayFiber {
    pub fn germ(&self) -> FieldGermId {
        match self {
            Self::Quadric { testimony, .. } | Self::Torus { testimony, .. } => testimony.germ,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenFieldRayFiber {
    pub testimony: FieldGermTestimony,
    pub support_fiber: ExactAffineVersionFiber,
    pub phases: BTreeMap<FieldPhaseChannel, ExactPhaseFiber>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldRaySeam {
    CoincidentSupport(FieldGermId),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldAtlasQueryWork {
    pub logical_germ_population: u64,
    pub active_germ_population: u64,
    pub pages: u64,
    pub peak_resident_germs: u64,
    pub resolved_supports: u64,
    pub unresolved_supports: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldReceiverReceipt {
    pub schema: String,
    pub receiver: ReceiverId,
    pub ray: crate::ExactRay,
    pub fibers: Vec<ExactFieldRayFiber>,
    pub open_fibers: Vec<OpenFieldRayFiber>,
    pub seams: Vec<FieldRaySeam>,
    pub work: FieldAtlasQueryWork,
}

/// A bounded physical view of one unmodified logical standing.
///
/// `page_germs` changes only the resident working set and resource receipt.
/// It cannot truncate or refuse a larger logical ecology.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalFieldAtlasMount {
    page_germs: usize,
}

impl CausalFieldAtlasMount {
    pub fn new(page_germs: usize) -> Result<Self, FieldAtlasError> {
        if page_germs == 0 {
            return Err(FieldAtlasError::ZeroResidentPage);
        }
        Ok(Self { page_germs })
    }

    pub fn receive(
        &self,
        standing: &CausalFieldStanding,
        query: &FieldReceiverQuery,
    ) -> Result<FieldReceiverReceipt, FieldAtlasError> {
        validate_standing(standing)?;
        if query.ray.direction == RatVec3::zero() {
            return Err(FieldAtlasError::ZeroQueryDirection);
        }
        let active = standing.active_germs().into_iter().collect::<Vec<_>>();
        let mut fibers = Vec::new();
        let mut open_fibers = Vec::new();
        let mut seams = Vec::new();
        for page in active.chunks(self.page_germs) {
            for germ_id in page {
                let germ = &standing.germs[germ_id];
                match &germ.support {
                    FieldSupportStanding::Quadric {
                        fiber,
                        resolved: None,
                        ..
                    } => open_fibers.push(OpenFieldRayFiber {
                        testimony: germ.into(),
                        support_fiber: fiber.clone(),
                        phases: germ.phases.clone(),
                    }),
                    FieldSupportStanding::Quadric {
                        resolved: Some(quadric),
                        coorientation: Some(coorientation),
                        ..
                    } => match quadric.ray_fiber_all(&query.ray.origin, &query.ray.direction) {
                        Ok(fiber) => fibers.push(ExactFieldRayFiber::Quadric {
                            testimony: germ.into(),
                            support: quadric.clone(),
                            coorientation: *coorientation,
                            fiber,
                            phases: germ.resolved_phase_laws(),
                        }),
                        Err(ImplicitError::CoincidentRay) => {
                            seams.push(FieldRaySeam::CoincidentSupport(*germ_id));
                        }
                        Err(error) => return Err(error.into()),
                    },
                    FieldSupportStanding::Quadric {
                        resolved: Some(_),
                        coorientation: None,
                        ..
                    } => return Err(FieldAtlasError::MalformedStanding),
                    FieldSupportStanding::Torus(torus) => {
                        match torus.ray_fiber_all(&query.ray.origin, &query.ray.direction) {
                            Ok(fiber) => fibers.push(ExactFieldRayFiber::Torus {
                                testimony: germ.into(),
                                support: torus.clone(),
                                fiber,
                                phases: germ.resolved_phase_laws(),
                            }),
                            Err(ImplicitError::CoincidentRay) => {
                                seams.push(FieldRaySeam::CoincidentSupport(*germ_id));
                            }
                            Err(error) => return Err(error.into()),
                        }
                    }
                }
            }
        }
        fibers.sort_by_key(ExactFieldRayFiber::germ);
        open_fibers.sort_by_key(|fiber| fiber.testimony.germ);
        seams.sort_by_key(|seam| match seam {
            FieldRaySeam::CoincidentSupport(germ) => *germ,
        });
        let pages = if active.is_empty() {
            0
        } else {
            active.len().div_ceil(self.page_germs)
        };
        let work = FieldAtlasQueryWork {
            logical_germ_population: usize_to_u64(standing.germs.len())?,
            active_germ_population: usize_to_u64(active.len())?,
            pages: usize_to_u64(pages)?,
            peak_resident_germs: usize_to_u64(active.len().min(self.page_germs))?,
            resolved_supports: usize_to_u64(fibers.len())?,
            unresolved_supports: usize_to_u64(open_fibers.len())?,
        };
        Ok(FieldReceiverReceipt {
            schema: "holonic-engine.field-receiver-receipt.v1".to_owned(),
            receiver: query.receiver,
            ray: query.ray.clone(),
            fibers,
            open_fibers,
            seams,
            work,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseBasis {
    pub receiver: ReceiverId,
    pub coordinates: [BTreeMap<FieldPhaseChannel, Rat>; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseProjection {
    pub receiver: ReceiverId,
    pub values: [Rat; 3],
    pub gradients: [RatVec3; 3],
}

pub fn project_germ_phase(
    germ: &CausalFieldGerm,
    point: &RatVec3,
    basis: &ReceiverPhaseBasis,
) -> Result<ReceiverPhaseProjection, FieldAtlasError> {
    let laws = germ.resolved_phase_laws();
    let mut values = std::array::from_fn(|_| Rat::zero());
    let mut gradients = std::array::from_fn(|_| RatVec3::zero());
    for coordinate in 0..3 {
        for (channel, weight) in &basis.coordinates[coordinate] {
            let law = laws
                .get(channel)
                .ok_or(FieldAtlasError::OpenPhaseChannel(*channel))?;
            values[coordinate] += weight * law.evaluate(point);
            gradients[coordinate] = gradients[coordinate].add(&law.gradient().scale(weight));
        }
    }
    Ok(ReceiverPhaseProjection {
        receiver: basis.receiver,
        values,
        gradients,
    })
}

fn usize_to_u64(value: usize) -> Result<u64, FieldAtlasError> {
    u64::try_from(value).map_err(|_| FieldAtlasError::CarrierOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum FieldAtlasError {
    #[error("a causal-field event must contain at least one occurrence")]
    EmptyEvent,
    #[error("causal-field event {0:?} has already entered standing")]
    RepeatedEvent(EventId),
    #[error("causal-field chronology {supplied} does not follow {previous}")]
    NoncausalChronology { previous: u64, supplied: u64 },
    #[error("one event supplied more than one image section for the same receiver")]
    DuplicateImageReceiver,
    #[error("an oriented field sample must name at least one local region")]
    EmptySampleRegion,
    #[error("an oriented field sample cannot have a zero normal")]
    ZeroSampleNormal,
    #[error("a declared field chart must name at least one ambient coordinate")]
    EmptyChart,
    #[error("a declared field chart cannot name one ambient coordinate twice")]
    RepeatedChartAxis,
    #[error("region {0:?} has already founded germs and cannot redeclare its chart")]
    RegionChartAfterFounding(FieldRegionId),
    #[error("a sample normal carries no component inside the declared chart {chart:?}")]
    SampleNormalOutsideChart { chart: FieldChart },
    #[error(
        "region {region:?} declares chart {chart:?}; a source torus carries an ambient center and axis"
    )]
    SourceTorusOutsideAmbientChart {
        region: FieldRegionId,
        chart: FieldChart,
    },
    #[error("region {region:?} declares chart {declared:?}; the supplied phase law reads {supplied:?}")]
    PhaseLawChartMismatch {
        region: FieldRegionId,
        declared: FieldChart,
        supplied: FieldChart,
    },
    #[error("an affine phase law in this chart requires {required} coefficients, not {supplied}")]
    PhaseLawCoefficientPopulation { required: usize, supplied: usize },
    #[error("the causal-field standing is malformed")]
    MalformedStanding,
    #[error("an image section is malformed")]
    MalformedImageSection,
    #[error("receiver {0:?} has no image section for the declared sample contact")]
    MissingContactImage(ReceiverId),
    #[error("image contact ({column},{row}) lies outside receiver {receiver:?}'s current aperture")]
    ImageContactOutsideAperture {
        receiver: ReceiverId,
        column: u32,
        row: u32,
    },
    #[error("receiver contact contradicts supplied phase channel {0:?}")]
    ConflictingContactPhase(FieldPhaseChannel),
    #[error(
        "source torus chronology {source_event:?}..{last_event:?} cannot enter event {event:?}"
    )]
    SourceTorusChronology {
        source_event: EventId,
        last_event: EventId,
        event: EventId,
    },
    #[error("implicit support identity {0:?} already exists in the field atlas")]
    DuplicateImplicitIdentity(ImplicitCellId),
    #[error("a freshly founded field germ rejected its own founding observation")]
    FreshGermObstructed,
    #[error("the exact quadric coefficient fiber is malformed")]
    MalformedQuadricFiber,
    #[error("the exact phase coefficient fiber is malformed")]
    MalformedPhaseFiber,
    #[error("field germ {0:?} is absent")]
    UnknownGerm(FieldGermId),
    #[error("physical field-atlas pages must contain at least one germ")]
    ZeroResidentPage,
    #[error("a receiver field query cannot use the zero direction")]
    ZeroQueryDirection,
    #[error("phase channel {0:?} remains open at this receiver query")]
    OpenPhaseChannel(FieldPhaseChannel),
    #[error("an exact field carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Diagram(#[from] DiagramError),
    #[error(transparent)]
    Receiver(#[from] ReceiverError),
    #[error(transparent)]
    Implicit(#[from] ImplicitError),
    #[error(transparent)]
    Inverse(#[from] InverseTransportError),
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use relational_geometry::integer;

    use super::*;
    use crate::{CausalWorld, ExactRay, ExactRgb};

    fn empty_event(event: u64, chronology: u64) -> CausalFieldEvent {
        CausalFieldEvent {
            event: EventId(event),
            chronology,
            images: Vec::new(),
            oriented_samples: Vec::new(),
            source_tori: Vec::new(),
        }
    }

    fn phase_law() -> ExactAffinePhaseLaw {
        ExactAffinePhaseLaw::new(
            FieldChart::ambient(),
            vec![integer(1), integer(2), integer(3), integer(4)],
        )
        .unwrap()
    }

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(numerator.into(), denominator.into())
    }

    /// Five exact rational points of `x^2 + y^2 = 4` in the plane `z = 0`,
    /// each carrying its radial in-plane normal.
    fn coplanar_circle_samples(region: FieldRegionId) -> Vec<OrientedFieldSample> {
        [
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(-2, 0, 0),
            RatVec3::from_i64(0, 2, 0),
            RatVec3::from_i64(0, -2, 0),
            RatVec3::new(rat(6, 5), rat(8, 5), integer(0)),
        ]
        .into_iter()
        .map(|point| OrientedFieldSample {
            regions: BTreeSet::from([region]),
            normal: point.clone(),
            point,
            phase: BTreeMap::new(),
            receiver_contact: None,
        })
        .collect()
    }

    fn resolve_under_chart(
        chart: FieldChart,
        samples: Vec<OrientedFieldSample>,
        region: FieldRegionId,
    ) -> (usize, usize, Option<ExactQuadric3>) {
        let law = CausalFieldAtlasLaw;
        let mut standing = law.initial_standing();
        standing.declare_region_chart(region, chart).unwrap();
        let mut event = empty_event(1, 1);
        event.oriented_samples = samples;
        let standing = law.enact(&standing, &event).unwrap().standing_after;
        let germ = standing.germs.values().next().unwrap();
        let FieldSupportStanding::Quadric {
            fiber, resolved, ..
        } = &germ.support
        else {
            panic!("an oriented sample founds a quadric germ");
        };
        (
            fiber.variable_count(),
            fiber.affine_dimension(),
            resolved.clone(),
        )
    }

    #[test]
    fn every_coefficient_population_is_read_off_the_declared_chart() {
        for (axes, dimension, quadric, affine) in [
            (vec![FieldChartAxis::X], 1_usize, 3_usize, 2_usize),
            (vec![FieldChartAxis::X, FieldChartAxis::Y], 2, 6, 3),
            (
                vec![FieldChartAxis::X, FieldChartAxis::Y, FieldChartAxis::Z],
                3,
                10,
                4,
            ),
        ] {
            let chart = FieldChart::new(axes).unwrap();
            assert_eq!(chart.dimension(), dimension);
            assert_eq!(chart.quadric_coefficient_count(), quadric);
            assert_eq!(
                chart.quadric_monomials().len(),
                chart.quadric_coefficient_count(),
                "the enumerated monomials must be exactly C(n+2,2)"
            );
            assert_eq!(chart.affine_coefficient_count(), affine);
            let tangents =
                chart_tangent_basis(&chart, &RatVec3::from_i64(1, 1, 1)).unwrap();
            assert_eq!(
                tangents.len(),
                dimension - 1,
                "a normal in n coordinates has n-1 tangents"
            );
        }
    }

    #[test]
    fn a_declared_chart_refuses_an_empty_or_repeated_coordinate_list() {
        assert_eq!(FieldChart::new(Vec::new()), Err(FieldAtlasError::EmptyChart));
        assert_eq!(
            FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::X]),
            Err(FieldAtlasError::RepeatedChartAxis)
        );
    }

    #[test]
    fn coplanar_material_resolves_in_its_own_chart_and_never_in_the_ambient_one() {
        let region = FieldRegionId(1);
        let (ambient_variables, ambient_dimension, ambient_resolved) = resolve_under_chart(
            FieldChart::ambient(),
            coplanar_circle_samples(region),
            region,
        );
        assert_eq!(ambient_variables, 10);
        assert_eq!(ambient_dimension, 2);
        assert_eq!(
            ambient_resolved, None,
            "in the ambient chart the coplanar pencil never collapses to one quadric"
        );

        let (plane_variables, plane_dimension, plane_resolved) = resolve_under_chart(
            FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap(),
            coplanar_circle_samples(region),
            region,
        );
        assert_eq!(plane_variables, 6);
        assert_eq!(plane_dimension, 1);
        let quadric = plane_resolved.expect("the same material resolves the conic in its plane");
        assert_eq!(
            quadric.coefficients,
            [
                integer(1),
                integer(1),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(-4),
            ],
            "the conic lifts to the ambient cylinder x^2 + y^2 - 4"
        );
    }

    #[test]
    fn a_coplanar_phase_resolves_in_its_own_chart_and_never_in_the_ambient_one() {
        let law = CausalFieldAtlasLaw;
        let region = FieldRegionId(11);
        let channel = FieldPhaseChannel::Declared(1);
        // `3x + 5y + 7`, read on material that never leaves the plane z = 0.
        let phase_of = |point: &RatVec3| {
            integer(3) * &point.x + integer(5) * &point.y + integer(7)
        };
        let samples = || {
            coplanar_circle_samples(region)
                .into_iter()
                .map(|mut sample| {
                    sample.phase = BTreeMap::from([(channel, phase_of(&sample.point))]);
                    sample
                })
                .collect::<Vec<_>>()
        };
        let resolved_phase = |chart: FieldChart| {
            let mut standing = law.initial_standing();
            standing.declare_region_chart(region, chart).unwrap();
            let mut event = empty_event(1, 1);
            event.oriented_samples = samples();
            let standing = law.enact(&standing, &event).unwrap().standing_after;
            let germ = standing.germs.values().next().unwrap();
            let fiber = &germ.phases[&channel];
            (fiber.fiber.variable_count(), fiber.law.clone())
        };

        let (ambient_variables, ambient_law) = resolved_phase(FieldChart::ambient());
        assert_eq!(ambient_variables, 4);
        assert_eq!(
            ambient_law, None,
            "coplanar material can never pivot the ambient chart's fourth coordinate"
        );

        let (plane_variables, plane_law) = resolved_phase(
            FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap(),
        );
        assert_eq!(plane_variables, 3);
        let plane_law = plane_law.expect("the same material resolves the affine law in its plane");
        assert_eq!(
            plane_law.coefficients(),
            [integer(3), integer(5), integer(7)]
        );
        assert_eq!(plane_law.gradient(), RatVec3::from_i64(3, 5, 0));
        assert_eq!(
            plane_law.evaluate(&RatVec3::from_i64(1, 1, 9)),
            integer(15),
            "the chart's law does not read the coordinate the chart does not name"
        );
    }

    #[test]
    fn a_one_coordinate_chart_resolves_a_binary_quadratic() {
        let region = FieldRegionId(3);
        let samples = [(2_i64, 1_i64), (-2, -1)]
            .into_iter()
            .map(|(position, orientation)| OrientedFieldSample {
                regions: BTreeSet::from([region]),
                point: RatVec3::from_i64(position, 0, 0),
                normal: RatVec3::from_i64(orientation, 0, 0),
                phase: BTreeMap::new(),
                receiver_contact: None,
            })
            .collect();
        let (variables, dimension, resolved) = resolve_under_chart(
            FieldChart::new(vec![FieldChartAxis::X]).unwrap(),
            samples,
            region,
        );
        assert_eq!(variables, 3);
        assert_eq!(dimension, 1);
        let quadric = resolved.expect("two oriented points resolve x^2 - 4 in a one-axis chart");
        assert_eq!(
            quadric.coefficients,
            [
                integer(1),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(-4),
            ]
        );
    }

    #[test]
    fn a_normal_with_no_component_in_the_declared_chart_is_refused_by_name() {
        let law = CausalFieldAtlasLaw;
        let region = FieldRegionId(5);
        let chart = FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap();
        let sample = |normal: RatVec3| OrientedFieldSample {
            regions: BTreeSet::from([region]),
            point: RatVec3::from_i64(2, 0, 0),
            normal,
            phase: BTreeMap::new(),
            receiver_contact: None,
        };
        let mut standing = law.initial_standing();
        standing.declare_region_chart(region, chart.clone()).unwrap();

        let mut refused = empty_event(1, 1);
        refused.oriented_samples = vec![sample(RatVec3::from_i64(0, 0, 1))];
        assert_eq!(
            law.enact(&standing, &refused),
            Err(FieldAtlasError::SampleNormalOutsideChart { chart })
        );

        let mut admitted = empty_event(1, 1);
        admitted.oriented_samples = vec![sample(RatVec3::from_i64(1, 0, 0))];
        assert!(
            law.enact(&standing, &admitted).is_ok(),
            "the same point with an in-chart normal is admitted"
        );
    }

    #[test]
    fn a_region_that_has_founded_cannot_redeclare_its_chart() {
        let law = CausalFieldAtlasLaw;
        let region = FieldRegionId(9);
        let mut event = empty_event(1, 1);
        event.oriented_samples = sphere_samples(region);
        let mut standing = law.enact(&law.initial_standing(), &event).unwrap().standing_after;
        assert_eq!(
            standing.declare_region_chart(
                region,
                FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap()
            ),
            Err(FieldAtlasError::RegionChartAfterFounding(region))
        );
        assert!(
            standing
                .declare_region_chart(
                    FieldRegionId(10),
                    FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap()
                )
                .is_ok(),
            "an unfounded region may still declare"
        );
    }

    #[test]
    fn a_phase_law_states_its_own_coefficient_population_and_its_own_chart() {
        let plane = FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap();
        assert_eq!(
            ExactAffinePhaseLaw::new(plane.clone(), vec![integer(1), integer(2), integer(3)])
                .map(|law| law.coefficients().len()),
            Ok(3)
        );
        assert_eq!(
            ExactAffinePhaseLaw::new(
                plane.clone(),
                vec![integer(1), integer(2), integer(3), integer(4)]
            ),
            Err(FieldAtlasError::PhaseLawCoefficientPopulation {
                required: 3,
                supplied: 4
            })
        );

        // A source torus is an ambient carrier, so a phase law read in a
        // proper sub-chart cannot be attached to one.
        let law = CausalFieldAtlasLaw;
        let region = FieldRegionId(12);
        let torus = || {
            ExactTorus::new(
                ImplicitCellId(1),
                EventId(1),
                RatVec3::zero(),
                RatVec3::from_i64(0, 0, 1),
                integer(3),
                integer(1),
            )
            .unwrap()
        };
        let occurrence = |phase: ExactAffinePhaseLaw| CausalFieldEvent {
            event: EventId(1),
            chronology: 1,
            images: Vec::new(),
            oriented_samples: Vec::new(),
            source_tori: vec![SourceTorusOccurrence {
                region,
                torus: torus(),
                phases: BTreeMap::from([(FieldPhaseChannel::Declared(1), phase)]),
            }],
        };
        let standing = law.initial_standing();
        assert_eq!(
            law.enact(
                &standing,
                &occurrence(
                    ExactAffinePhaseLaw::new(
                        plane.clone(),
                        vec![integer(1), integer(2), integer(3)]
                    )
                    .unwrap()
                )
            ),
            Err(FieldAtlasError::PhaseLawChartMismatch {
                region,
                declared: FieldChart::ambient(),
                supplied: plane,
            })
        );
        assert!(
            law.enact(&standing, &occurrence(phase_law())).is_ok(),
            "the same torus with an ambient phase law is admitted"
        );
    }

    #[test]
    fn a_source_torus_is_refused_in_a_proper_sub_chart() {
        let law = CausalFieldAtlasLaw;
        let region = FieldRegionId(2);
        let chart = FieldChart::new(vec![FieldChartAxis::X, FieldChartAxis::Y]).unwrap();
        let mut standing = law.initial_standing();
        standing.declare_region_chart(region, chart.clone()).unwrap();
        let mut event = empty_event(1, 1);
        event.source_tori.push(SourceTorusOccurrence {
            region,
            torus: ExactTorus::new(
                ImplicitCellId(1),
                EventId(1),
                RatVec3::zero(),
                RatVec3::from_i64(0, 0, 1),
                integer(3),
                integer(1),
            )
            .unwrap(),
            phases: BTreeMap::new(),
        });
        assert_eq!(
            law.enact(&standing, &event),
            Err(FieldAtlasError::SourceTorusOutsideAmbientChart { region, chart })
        );
    }

    fn sphere_samples(region: FieldRegionId) -> Vec<OrientedFieldSample> {
        [
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(-2, 0, 0),
            RatVec3::from_i64(0, 2, 0),
            RatVec3::from_i64(0, -2, 0),
            RatVec3::from_i64(0, 0, 2),
            RatVec3::from_i64(0, 0, -2),
        ]
        .into_iter()
        .map(|point| OrientedFieldSample {
            regions: BTreeSet::from([region]),
            normal: point.clone(),
            phase: BTreeMap::from([(FieldPhaseChannel::Declared(1), phase_law().evaluate(&point))]),
            point,
            receiver_contact: None,
        })
        .collect()
    }

    #[test]
    fn caused_samples_resolve_curvature_phase_gradient_and_plural_depth() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        event.oriented_samples = sphere_samples(FieldRegionId(7));
        let successor = law.enact(&law.initial_standing(), &event).unwrap();
        let standing = successor.standing_after;
        assert_eq!(standing.germs.len(), 1);
        let germ = standing.germs.values().next().unwrap();
        let FieldSupportStanding::Quadric {
            resolved: Some(quadric),
            ..
        } = &germ.support
        else {
            panic!("six oriented sections must resolve the sphere quadric");
        };
        assert_eq!(
            quadric.coefficients,
            [
                integer(1),
                integer(1),
                integer(1),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(-4),
            ]
        );
        assert_eq!(
            germ.support.gradient(&RatVec3::from_i64(2, 0, 0)),
            Some(RatVec3::from_i64(4, 0, 0))
        );
        assert_eq!(
            germ.phases[&FieldPhaseChannel::Declared(1)]
                .law
                .as_ref()
                .unwrap()
                .gradient(),
            RatVec3::from_i64(1, 2, 3)
        );

        let receipt = CausalFieldAtlasMount::new(1)
            .unwrap()
            .receive(
                &standing,
                &FieldReceiverQuery {
                    receiver: ReceiverId(9),
                    ray: ExactRay {
                        origin: RatVec3::from_i64(-3, 0, 0),
                        direction: RatVec3::from_i64(1, 0, 0),
                    },
                },
            )
            .unwrap();
        let ExactFieldRayFiber::Quadric {
            testimony,
            coorientation,
            fiber,
            ..
        } = &receipt.fibers[0]
        else {
            panic!("the derived germ must remain a quadric");
        };
        assert_eq!(*coorientation, FieldCoorientation::AlongCanonical);
        assert_eq!(testimony.lineage, BTreeSet::from([EventId(1)]));
        assert_eq!(testimony.origin, FieldGermOrigin::DerivedFromObservation);
        assert_eq!(fiber.roots.len(), 2);
        assert!(receipt.open_fibers.is_empty());
    }

    #[test]
    fn derived_support_retains_observed_coorientation() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        event.oriented_samples = sphere_samples(FieldRegionId(1))
            .into_iter()
            .map(|mut sample| {
                sample.normal = sample.normal.scale(&integer(-1));
                sample
            })
            .collect();
        let standing = law
            .enact(&law.initial_standing(), &event)
            .unwrap()
            .standing_after;
        let germ = standing.germs.values().next().unwrap();
        let FieldSupportStanding::Quadric { coorientation, .. } = &germ.support else {
            panic!("the observed support must be the derived quadric");
        };
        assert_eq!(*coorientation, Some(FieldCoorientation::AgainstCanonical));
        assert_eq!(
            germ.support.gradient(&RatVec3::from_i64(2, 0, 0)),
            Some(RatVec3::from_i64(-4, 0, 0))
        );
    }

    #[test]
    fn obstruction_emanates_a_descendant_and_exposes_its_causal_cones() {
        let law = CausalFieldAtlasLaw;
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let mut founding = empty_event(1, 1);
        founding.oriented_samples = sphere_samples(FieldRegionId(1));
        world.receive(&founding).unwrap();
        let parent = *world.standing().germs.keys().next().unwrap();

        let mut obstruction = empty_event(2, 2);
        obstruction.oriented_samples.push(OrientedFieldSample {
            regions: BTreeSet::from([FieldRegionId(1)]),
            point: RatVec3::zero(),
            normal: RatVec3::from_i64(1, 0, 0),
            phase: BTreeMap::new(),
            receiver_contact: None,
        });
        let receipt = world.receive(&obstruction).unwrap();
        let radiation = &receipt.radiation[0];
        assert_eq!(world.standing().germs.len(), 2);
        assert_eq!(radiation.emanations.len(), 1);
        let child = *radiation.founded_germs.iter().next().unwrap();
        assert_eq!(
            world.standing().future_cone(parent).unwrap(),
            BTreeSet::from([parent, child])
        );
        assert_eq!(
            world.standing().past_cone(child).unwrap(),
            BTreeSet::from([parent, child])
        );
        assert_eq!(
            world.standing().active_regions[&FieldRegionId(1)],
            BTreeSet::from([parent, child])
        );

        let mut second_obstruction = empty_event(3, 3);
        second_obstruction
            .oriented_samples
            .push(OrientedFieldSample {
                regions: BTreeSet::from([FieldRegionId(1)]),
                point: RatVec3::from_i64(1, 0, 0),
                normal: RatVec3::from_i64(0, 1, 0),
                phase: BTreeMap::new(),
                receiver_contact: None,
            });
        world.receive(&second_obstruction).unwrap();
        assert!(
            world.standing().future_cone(parent).unwrap().len() >= 3,
            "successive incompatible arrivals must be able to diverge from one causal germ"
        );
    }

    #[test]
    fn logical_population_outgrows_the_rejected_locus_ceiling() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        event.oriented_samples = (0..513)
            .map(|region| OrientedFieldSample {
                regions: BTreeSet::from([FieldRegionId(region)]),
                point: RatVec3::from_i64(i64::try_from(region).unwrap(), 0, 0),
                normal: RatVec3::from_i64(0, 1, 0),
                phase: BTreeMap::new(),
                receiver_contact: None,
            })
            .collect();
        let successor = law.enact(&law.initial_standing(), &event).unwrap();
        assert_eq!(successor.standing_after.germs.len(), 513);
        assert_eq!(
            successor.radiation[0].germ_population_after, 513,
            "there is no maximum-locus specification or refusal"
        );
    }

    #[test]
    fn bounded_resident_pages_return_the_same_exact_field() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        for index in 0..20_u64 {
            event.source_tori.push(SourceTorusOccurrence {
                region: FieldRegionId(index),
                torus: ExactTorus::new(
                    ImplicitCellId(index + 1),
                    EventId(1),
                    RatVec3::from_i64(0, i64::try_from(index).unwrap(), 0),
                    RatVec3::from_i64(0, 0, 1),
                    integer(3),
                    integer(1),
                )
                .unwrap(),
                phases: BTreeMap::from([(FieldPhaseChannel::Declared(1), phase_law())]),
            });
        }
        let standing = law
            .enact(&law.initial_standing(), &event)
            .unwrap()
            .standing_after;
        let query = FieldReceiverQuery {
            receiver: ReceiverId(1),
            ray: ExactRay {
                origin: RatVec3::from_i64(-5, 0, 0),
                direction: RatVec3::from_i64(1, 0, 0),
            },
        };
        let one = CausalFieldAtlasMount::new(1)
            .unwrap()
            .receive(&standing, &query)
            .unwrap();
        let all = CausalFieldAtlasMount::new(64)
            .unwrap()
            .receive(&standing, &query)
            .unwrap();
        assert_eq!(one.fibers, all.fibers);
        assert_eq!(one.open_fibers, all.open_fibers);
        assert_eq!(one.seams, all.seams);
        assert_eq!(one.work.pages, 20);
        assert_eq!(all.work.pages, 1);
        assert_eq!(one.work.peak_resident_germs, 1);
        assert_eq!(all.work.peak_resident_germs, 20);
        assert!(
            standing
                .germs
                .values()
                .all(|germ| matches!(germ.origin, FieldGermOrigin::SourceTorus { .. }))
        );
    }

    #[test]
    fn complete_images_grow_as_sections_without_pixel_world_cells() {
        let law = CausalFieldAtlasLaw;
        let rays = RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        };
        let raster = |last| {
            ExactRaster::new(
                ImageExtent {
                    width: 2,
                    height: 1,
                },
                vec![
                    ExactRgb {
                        red: 10,
                        green: 20,
                        blue: 30,
                    },
                    last,
                ],
            )
            .unwrap()
        };
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let mut first = empty_event(1, 1);
        first.images.push(ReceiverImageOccurrence {
            receiver: ReceiverId(4),
            rays: rays.clone(),
            raster: raster(ExactRgb {
                red: 40,
                green: 50,
                blue: 60,
            }),
        });
        world.receive(&first).unwrap();
        let mut second = empty_event(2, 2);
        second.images.push(ReceiverImageOccurrence {
            receiver: ReceiverId(4),
            rays,
            raster: raster(ExactRgb {
                red: 41,
                green: 48,
                blue: 63,
            }),
        });
        world.receive(&second).unwrap();
        assert_eq!(world.standing().images.len(), 2);
        assert_eq!(world.standing().image_differences.len(), 1);
        assert!(world.standing().germs.is_empty());
        assert!(world.standing().observations.is_empty());
        let ImageSectionComparison::CommonAperture { departures } =
            &world.standing().image_differences[0].comparison
        else {
            panic!("the aperture did not change");
        };
        assert_eq!(
            departures,
            &[ImageSampleDeparture {
                column: 1,
                row: 0,
                channels: [1, -2, 3],
            }]
        );
    }

    #[test]
    fn receiver_basis_projects_resolved_phase_value_and_gradient() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        event.oriented_samples = sphere_samples(FieldRegionId(1));
        let standing = law
            .enact(&law.initial_standing(), &event)
            .unwrap()
            .standing_after;
        let germ = standing.germs.values().next().unwrap();
        let basis = ReceiverPhaseBasis {
            receiver: ReceiverId(8),
            coordinates: [
                BTreeMap::from([(FieldPhaseChannel::Declared(1), integer(1))]),
                BTreeMap::from([(FieldPhaseChannel::Declared(1), integer(2))]),
                BTreeMap::from([(FieldPhaseChannel::Declared(1), integer(-1))]),
            ],
        };
        let projection = project_germ_phase(germ, &RatVec3::from_i64(1, 1, 1), &basis).unwrap();
        assert_eq!(projection.values, [integer(10), integer(20), integer(-10)]);
        assert_eq!(
            projection.gradients,
            [
                RatVec3::from_i64(1, 2, 3),
                RatVec3::from_i64(2, 4, 6),
                RatVec3::from_i64(-1, -2, -3),
            ]
        );
    }

    #[test]
    fn image_contacts_refine_receiver_phase_without_promoting_pixels_to_world_cells() {
        let law = CausalFieldAtlasLaw;
        let receiver = ReceiverId(12);
        let points = [
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(-2, 0, 0),
            RatVec3::from_i64(0, 2, 0),
            RatVec3::from_i64(0, 0, 2),
        ];
        let phase = phase_law();
        let colors = points
            .iter()
            .map(|point| {
                let value = phase.evaluate(point).to_integer().try_into().unwrap();
                ExactRgb {
                    red: value,
                    green: value * 2,
                    blue: value * 3,
                }
            })
            .collect();
        let mut event = empty_event(1, 1);
        event.images.push(ReceiverImageOccurrence {
            receiver,
            rays: RayFamily::Central {
                center: RatVec3::zero(),
                forward: RatVec3::from_i64(0, 0, 1),
                horizontal: RatVec3::from_i64(1, 0, 0),
                vertical: RatVec3::from_i64(0, 1, 0),
            },
            raster: ExactRaster::new(
                ImageExtent {
                    width: 2,
                    height: 2,
                },
                colors,
            )
            .unwrap(),
        });
        event.oriented_samples = points
            .into_iter()
            .enumerate()
            .map(|(index, point)| OrientedFieldSample {
                regions: BTreeSet::from([FieldRegionId(1)]),
                normal: point.clone(),
                point,
                phase: BTreeMap::new(),
                receiver_contact: Some(ReceiverSampleContact {
                    receiver,
                    column: u32::try_from(index % 2).unwrap(),
                    row: u32::try_from(index / 2).unwrap(),
                }),
            })
            .collect();

        let standing = law
            .enact(&law.initial_standing(), &event)
            .unwrap()
            .standing_after;
        assert_eq!(standing.images.len(), 1);
        assert_eq!(standing.observations.len(), 4);
        assert_eq!(standing.germs.len(), 1);
        let germ = standing.germs.values().next().unwrap();
        for (coordinate, scale) in [(0, 1), (1, 2), (2, 3)] {
            let channel = FieldPhaseChannel::ReceiverCoordinate {
                receiver,
                coordinate,
            };
            assert_eq!(
                germ.phases[&channel].law.as_ref().unwrap().gradient(),
                RatVec3::from_i64(scale, scale * 2, scale * 3)
            );
        }
    }

    #[test]
    fn exact_standing_rests_remounts_and_returns_the_same_receiver_field() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        event.oriented_samples = sphere_samples(FieldRegionId(1));
        let standing = law
            .enact(&law.initial_standing(), &event)
            .unwrap()
            .standing_after;
        let encoded = ron::to_string(&standing).unwrap();
        let remounted: CausalFieldStanding = ron::from_str(&encoded).unwrap();
        assert_eq!(standing, remounted);

        let query = FieldReceiverQuery {
            receiver: ReceiverId(5),
            ray: ExactRay {
                origin: RatVec3::from_i64(-3, 0, 0),
                direction: RatVec3::from_i64(1, 0, 0),
            },
        };
        let mount = CausalFieldAtlasMount::new(2).unwrap();
        assert_eq!(
            mount.receive(&standing, &query).unwrap(),
            mount.receive(&remounted, &query).unwrap()
        );
    }

    #[test]
    fn refused_event_cannot_partially_change_standing() {
        let law = CausalFieldAtlasLaw;
        let standing = law.initial_standing();
        let mut event = empty_event(1, 1);
        event.oriented_samples.push(OrientedFieldSample {
            regions: BTreeSet::from([FieldRegionId(1)]),
            point: RatVec3::zero(),
            normal: RatVec3::zero(),
            phase: BTreeMap::new(),
            receiver_contact: None,
        });
        assert_eq!(
            law.enact(&standing, &event),
            Err(FieldAtlasError::ZeroSampleNormal)
        );
        assert_eq!(standing, law.initial_standing());
    }

    #[test]
    fn logical_resource_work_counts_occurrences_not_resident_capacity() {
        let law = CausalFieldAtlasLaw;
        let mut event = empty_event(1, 1);
        event.oriented_samples = sphere_samples(FieldRegionId(1));
        let successor = law.enact(&law.initial_standing(), &event).unwrap();
        assert_eq!(
            successor.logical_resources.unwrap().work,
            BigUint::from(6_u8)
        );
    }
}
