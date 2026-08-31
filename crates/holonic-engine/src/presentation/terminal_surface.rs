//! Exact terminal surface receiver: finite cells, support fibers, and occlusion.

use super::*;

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

    pub(super) fn contains(&self, point: &[Rat; 2]) -> bool {
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

/// The exact source member which contributes to one terminal aperture cell.
///
/// A primitive may contribute more than once when a source thread has several
/// declared segments crossing one cell. The segment address remains separate
/// from the primitive identity so a display quotient cannot merge source
/// incidence merely because projected pieces share an address.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SurfaceMemberId {
    pub key: PresentedPrimitiveKey,
    pub segment: Option<usize>,
}

/// Exact support evidence for one source member inside a terminal cell.
///
/// Area fractions are used only for two-dimensional triangle support. A thread
/// carries its exact source-parameter interval instead: a line has no area
/// until a downstream display gauge declares a stroke law. Conics are
/// currently support-certified but retain `SupportOnly` until an exact arc
/// measure is admitted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SurfaceCoverage {
    AreaFraction(Rat),
    SourceParameterInterval { start: Rat, end: Rat },
    SupportOnly,
}

/// Exact depth evidence carried by one cell contribution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SurfaceDepth {
    /// `near` and `far` are receiver ray parameters; smaller is nearer.
    Range { near: Rat, far: Rat },
    /// The source member is supported, but this prototype has no depth law
    /// for its current representation.
    Unavailable,
    /// The depth denominator changes sign or reaches the projective horizon
    /// over the supported cell region.
    OpenProjective,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SurfaceContribution {
    pub member: SurfaceMemberId,
    pub support: ExactCellSupport,
    pub coverage: SurfaceCoverage,
    pub depth: SurfaceDepth,
}

/// Why a terminal cell cannot be reduced to one front-to-back layer order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OcclusionObstruction {
    MissingDepth,
    OpenProjectiveDepth,
    OverlappingDepthRanges,
    EqualDepth,
}

/// The receiver's exact occlusion return for one cell.
///
/// `Open` is a real result. It prevents the raster codec from inventing a
/// winner where the declared receiver has not proved one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OcclusionFace {
    Empty,
    Ordered {
        front_to_back: Vec<SurfaceMemberId>,
    },
    Open {
        members: Vec<SurfaceMemberId>,
        reason: OcclusionObstruction,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSurfaceCell {
    pub address: PresentationAddress,
    pub cell: ExactCell,
    pub contributions: Vec<SurfaceContribution>,
    pub occlusion: OcclusionFace,
}

/// A finite receiver aperture carrying exact occupied-cell support and depth fibers.
///
/// This is still a presentation face, not screen-owned world geometry. The
/// integer raster/colour codec is downstream and cannot change these cells.
/// Empty terminal cells are omitted from `cells` and are implied by the
/// declared terminal specification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSurfacePresentation {
    pub schema: String,
    pub specification: TerminalMatrixSpec,
    pub cells: BTreeMap<PresentationAddress, ExactSurfaceCell>,
    /// Receiver-work testimony. These counts do not participate in surface
    /// identity or in candidate admission.
    pub candidate_cells: BigUint,
    pub primitive_evaluations: BigUint,
    pub occupied_cells: BigUint,
    pub open_occlusion_cells: BigUint,
}

/// One source primitive's addressed work section.
///
/// The section is the smallest independent receiver passage in this pass:
/// its address population is derived from that primitive's exact support
/// cover, and no other primitive is visited while the section is evaluated.
/// The address list is a cover only; `surface_contributions_for_primitive`
/// remains the exact admission test for each cell.
#[derive(Clone, Debug)]
struct SurfacePrimitiveSection {
    primitive: PresentedPrimitive,
    addresses: Vec<PresentationAddress>,
}

/// Form exact cell-level coverage and conservative depth ordering from an
/// already assembled continuous presentation.
///
/// The terminal address supplies only the cell boundary. Source support is
/// obtained from existing primitive incidence; no neighboring pixels or
/// displayed points are joined. If a total depth order is not certified, the
/// complete competing population remains in `OcclusionFace::Open`.
pub fn exact_surface_presentation(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
) -> Result<ExactSurfacePresentation, PresentationError> {
    exact_surface_presentation_with_executor(presentation, specification, &CpuExecutor::serial())
        .map(|(surface, _execution)| surface)
}

/// Execute the exact surface receiver over independent primitive-address
/// sections. The executor controls only physical work placement; indexed
/// return order is canonical and therefore does not become surface identity.
pub fn exact_surface_presentation_with_executor(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    executor: &CpuExecutor,
) -> Result<(ExactSurfacePresentation, CpuExecutionReceipt), PresentationError> {
    specification.validate()?;
    let sections = candidate_surface_sections(presentation, specification)?;
    let mut candidate_address_cells = BTreeMap::new();
    for section in &sections {
        for address in &section.addresses {
            if !candidate_address_cells.contains_key(address) {
                candidate_address_cells.insert(*address, specification.cell(*address)?);
            }
        }
    }
    let candidate_cells = BigUint::from(candidate_address_cells.len());
    let primitive_evaluations = BigUint::from(
        sections
            .iter()
            .map(|section| section.addresses.len())
            .sum::<usize>(),
    );

    let (section_contributions, execution) = executor
        .execute_indexed(&sections, |_section_index, section| {
            let contributions = section
                .addresses
                .iter()
                .filter_map(|address| {
                    let cell = candidate_address_cells
                        .get(address)
                        .expect("candidate address cell was prepared before execution");
                    let contributions =
                        surface_contributions_for_primitive(&section.primitive, cell);
                    (!contributions.is_empty()).then_some((*address, contributions))
                })
                .collect::<Vec<_>>();
            Ok::<_, std::convert::Infallible>(contributions)
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => match error {},
            CpuExecutionError::WorkerPanicked => PresentationError::WorkerPanicked,
        })?;

    let mut contributions_by_address: BTreeMap<PresentationAddress, Vec<SurfaceContribution>> =
        BTreeMap::new();
    for section in section_contributions {
        for (address, contributions) in section {
            contributions_by_address
                .entry(address)
                .or_default()
                .extend(contributions);
        }
    }

    let mut cells = BTreeMap::new();
    let mut occupied_cells = BigUint::zero();
    let mut open_occlusion_cells = BigUint::zero();

    for (address, cell) in candidate_address_cells {
        let Some(contributions) = contributions_by_address.remove(&address) else {
            continue;
        };
        if contributions.is_empty() {
            continue;
        }
        let occlusion = occlusion_face(&contributions);
        occupied_cells += BigUint::one();
        if matches!(occlusion, OcclusionFace::Open { .. }) {
            open_occlusion_cells += BigUint::one();
        }
        cells.insert(
            address,
            ExactSurfaceCell {
                address,
                cell,
                contributions,
                occlusion,
            },
        );
    }

    Ok((
        ExactSurfacePresentation {
            schema: "holonic-engine.exact-surface-presentation.v1".to_owned(),
            specification: specification.clone(),
            cells,
            candidate_cells,
            primitive_evaluations,
            occupied_cells,
            open_occlusion_cells,
        },
        execution,
    ))
}

fn candidate_surface_sections(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
) -> Result<Vec<SurfacePrimitiveSection>, PresentationError> {
    let mut sections = Vec::with_capacity(presentation.primitives.len());
    let all_addresses = || specification.addresses().unwrap_or_default();

    // Add exact projected bounding boxes for finite linear primitives. A box
    // is only a candidate cover; the exact primitive/cell test below decides
    // whether the source member actually contributes.
    for presented in &presentation.primitives {
        let mut addresses = BTreeSet::new();
        let points = match &presented.primitive {
            ReceiverPrimitive::Triangle(triangle) => triangle
                .vertices
                .iter()
                .map(ProjectivePoint2::affine)
                .collect::<Option<Vec<_>>>(),
            ReceiverPrimitive::Thread(thread) => thread
                .vertices
                .iter()
                .map(ProjectivePoint2::affine)
                .collect::<Option<Vec<_>>>(),
            ReceiverPrimitive::Conic(conic) => {
                let terminal = ExactTerminalConic::new(&conic.form, specification)?;
                let mut regions = vec![ApertureRegion::complete(specification)];
                while let Some(region) = regions.pop() {
                    if !terminal.crosses(region) {
                        continue;
                    }
                    if region.right - region.left <= EXACT_COVER_TILE
                        && region.bottom - region.top <= EXACT_COVER_TILE
                    {
                        for row in region.top..region.bottom {
                            for column in region.left..region.right {
                                addresses.insert(PresentationAddress { column, row });
                            }
                        }
                    } else {
                        regions.extend(region.divide());
                    }
                }
                append_surface_sections(&mut sections, presented, addresses);
                continue;
            }
        };
        let Some(points) = points else {
            addresses.extend(all_addresses());
            append_surface_sections(&mut sections, presented, addresses);
            continue;
        };
        let horizontal = points
            .iter()
            .map(|point| point[0].clone())
            .collect::<Vec<_>>();
        let vertical = points
            .iter()
            .map(|point| point[1].clone())
            .collect::<Vec<_>>();
        let Some(columns) = bounding_axis_indices(
            &horizontal,
            &specification.boundary.horizontal_span,
            specification.width,
            false,
        ) else {
            addresses.extend(all_addresses());
            append_surface_sections(&mut sections, presented, addresses);
            continue;
        };
        let Some(rows) = bounding_axis_indices(
            &vertical,
            &specification.boundary.vertical_span,
            specification.height,
            true,
        ) else {
            addresses.extend(all_addresses());
            append_surface_sections(&mut sections, presented, addresses);
            continue;
        };
        for row in rows.0..=rows.1 {
            for column in columns.0..=columns.1 {
                addresses.insert(PresentationAddress { column, row });
            }
        }
        append_surface_sections(&mut sections, presented, addresses);
    }
    Ok(sections)
}

fn append_surface_sections(
    sections: &mut Vec<SurfacePrimitiveSection>,
    presented: &PresentedPrimitive,
    addresses: BTreeSet<PresentationAddress>,
) {
    let addresses = addresses.into_iter().collect::<Vec<_>>();
    for chunk in addresses.chunks(EXACT_WORK_CHUNK_CELLS) {
        sections.push(SurfacePrimitiveSection {
            primitive: presented.clone(),
            addresses: chunk.to_vec(),
        });
    }
}

fn bounding_axis_indices(
    values: &[Rat],
    span: &Rat,
    count: u32,
    invert: bool,
) -> Option<(u32, u32)> {
    if values.is_empty() || count == 0 || !span.is_positive() {
        return None;
    }
    let half = span / Rat::from_integer(2.into());
    let transformed = values
        .iter()
        .map(|value| if invert { &half - value } else { value + &half })
        .collect::<Vec<_>>();
    let minimum = transformed.iter().min()?;
    let maximum = transformed.iter().max()?;
    let count = BigInt::from(count);
    let scale = Rat::from_integer(count.clone()) / span;
    let minimum = minimum * &scale;
    let maximum = maximum * scale;
    if maximum < Rat::zero() || minimum > Rat::from_integer(count.clone()) {
        return None;
    }
    let minimum = floor_rational(&minimum).to_i64()?;
    let maximum = floor_rational(&maximum).to_i64()?;
    let last = count.to_i64()?.saturating_sub(1);
    Some((
        minimum.saturating_sub(1).clamp(0, last) as u32,
        maximum.saturating_add(1).clamp(0, last) as u32,
    ))
}

fn surface_contributions_for_primitive(
    presented: &PresentedPrimitive,
    cell: &ExactCell,
) -> Vec<SurfaceContribution> {
    let key = PresentedPrimitiveKey {
        receiver: presented.receiver,
        primitive: presented.primitive.id(),
    };
    match &presented.primitive {
        ReceiverPrimitive::Triangle(triangle) => {
            let Some(points) = triangle
                .vertices
                .iter()
                .map(ProjectivePoint2::affine)
                .collect::<Option<Vec<_>>>()
            else {
                return vec![SurfaceContribution {
                    member: SurfaceMemberId { key, segment: None },
                    support: ExactCellSupport::OpenProjective,
                    coverage: SurfaceCoverage::SupportOnly,
                    depth: SurfaceDepth::OpenProjective,
                }];
            };

            let clipped = clip_polygon_to_cell(&points, cell);
            if clipped.len() < 2 {
                return Vec::new();
            }
            let area = polygon_area(&clipped);
            let support = if area.is_zero() {
                ExactCellSupport::Boundary
            } else {
                ExactCellSupport::Interior
            };
            let coverage = if area.is_zero() {
                SurfaceCoverage::SupportOnly
            } else {
                let cell_width = &cell.upper[0] - &cell.lower[0];
                let cell_height = &cell.upper[1] - &cell.lower[1];
                SurfaceCoverage::AreaFraction(area / (cell_width * cell_height))
            };
            vec![SurfaceContribution {
                member: SurfaceMemberId { key, segment: None },
                support,
                coverage,
                depth: triangle_depth_over_polygon(triangle, &clipped),
            }]
        }
        ReceiverPrimitive::Thread(thread) => {
            let segment_count = thread
                .vertices
                .len()
                .saturating_sub(1)
                .saturating_add(usize::from(thread.closed && thread.vertices.len() > 1));
            (0..segment_count)
                .filter_map(|segment| {
                    let start = thread.vertices[segment].affine()?;
                    let next = (segment + 1) % thread.vertices.len();
                    let end = thread.vertices[next].affine()?;
                    let (start_parameter, end_parameter) =
                        clip_segment_parameter_to_cell(&start, &end, cell)?;
                    Some(SurfaceContribution {
                        member: SurfaceMemberId {
                            key: key.clone(),
                            segment: Some(segment),
                        },
                        support: ExactCellSupport::Boundary,
                        coverage: SurfaceCoverage::SourceParameterInterval {
                            start: start_parameter,
                            end: end_parameter,
                        },
                        // `ContinuousPresentation` does not carry the
                        // originating RayFamily beside a thread. Keeping
                        // this open is safer than choosing an interpolation
                        // law from projected endpoints.
                        depth: SurfaceDepth::Unavailable,
                    })
                })
                .collect()
        }
        ReceiverPrimitive::Conic(_) => primitive_cell_support(&presented.primitive, cell)
            .map(|support| SurfaceContribution {
                member: SurfaceMemberId { key, segment: None },
                support,
                coverage: SurfaceCoverage::SupportOnly,
                depth: SurfaceDepth::Unavailable,
            })
            .into_iter()
            .collect(),
    }
}

fn triangle_depth_over_polygon(triangle: &ProjectedTriangle, polygon: &[[Rat; 2]]) -> SurfaceDepth {
    let Some(law) = triangle.receiver_depth.as_deref() else {
        return SurfaceDepth::Unavailable;
    };
    let values = polygon
        .iter()
        .filter_map(|point| {
            let point =
                ProjectivePoint2::new(point[0].clone(), point[1].clone(), Rat::one()).ok()?;
            let denominator = &law.denominator.a * &point.x
                + &law.denominator.b * &point.y
                + &law.denominator.c * &point.w;
            if denominator.is_zero() {
                return None;
            }
            law.evaluate(&point)
        })
        .collect::<Vec<_>>();
    if values.len() != polygon.len() {
        return SurfaceDepth::OpenProjective;
    }
    let positive = values.iter().all(Rat::is_positive);
    let negative = values.iter().all(Rat::is_negative);
    if !positive && !negative {
        return SurfaceDepth::OpenProjective;
    }
    SurfaceDepth::Range {
        near: values.iter().min().expect("nonempty polygon").clone(),
        far: values.iter().max().expect("nonempty polygon").clone(),
    }
}

fn occlusion_face(contributions: &[SurfaceContribution]) -> OcclusionFace {
    if contributions.is_empty() {
        return OcclusionFace::Empty;
    }
    if contributions.len() == 1 {
        return OcclusionFace::Ordered {
            front_to_back: vec![contributions[0].member.clone()],
        };
    }
    if contributions
        .iter()
        .any(|contribution| matches!(contribution.depth, SurfaceDepth::Unavailable))
    {
        return OcclusionFace::Open {
            members: contributions
                .iter()
                .map(|contribution| contribution.member.clone())
                .collect(),
            reason: OcclusionObstruction::MissingDepth,
        };
    }
    if contributions
        .iter()
        .any(|contribution| matches!(contribution.depth, SurfaceDepth::OpenProjective))
    {
        return OcclusionFace::Open {
            members: contributions
                .iter()
                .map(|contribution| contribution.member.clone())
                .collect(),
            reason: OcclusionObstruction::OpenProjectiveDepth,
        };
    }

    let mut ordered = contributions.iter().collect::<Vec<_>>();
    ordered.sort_by(|left, right| {
        depth_near(&left.depth)
            .cmp(depth_near(&right.depth))
            .then_with(|| left.member.cmp(&right.member))
    });
    for pair in ordered.windows(2) {
        let left = depth_far(&pair[0].depth);
        let right = depth_near(&pair[1].depth);
        if left >= right {
            let reason =
                if left == right && depth_near(&pair[0].depth) == depth_near(&pair[1].depth) {
                    OcclusionObstruction::EqualDepth
                } else {
                    OcclusionObstruction::OverlappingDepthRanges
                };
            return OcclusionFace::Open {
                members: contributions
                    .iter()
                    .map(|contribution| contribution.member.clone())
                    .collect(),
                reason,
            };
        }
    }
    OcclusionFace::Ordered {
        front_to_back: ordered
            .into_iter()
            .map(|contribution| contribution.member.clone())
            .collect(),
    }
}

fn depth_near(depth: &SurfaceDepth) -> &Rat {
    match depth {
        SurfaceDepth::Range { near, .. } => near,
        SurfaceDepth::Unavailable | SurfaceDepth::OpenProjective => {
            unreachable!("open depth is rejected before ordering")
        }
    }
}

fn depth_far(depth: &SurfaceDepth) -> &Rat {
    match depth {
        SurfaceDepth::Range { far, .. } => far,
        SurfaceDepth::Unavailable | SurfaceDepth::OpenProjective => {
            unreachable!("open depth is rejected before ordering")
        }
    }
}

fn clip_polygon_to_cell(points: &[[Rat; 2]], cell: &ExactCell) -> Vec<[Rat; 2]> {
    let mut clipped = points.to_vec();
    for boundary in 0..4 {
        let (axis, bound, keep_greater) = match boundary {
            0 => (0, cell.lower[0].clone(), true),
            1 => (0, cell.upper[0].clone(), false),
            2 => (1, cell.lower[1].clone(), true),
            3 => (1, cell.upper[1].clone(), false),
            _ => unreachable!(),
        };
        clipped = clip_polygon_edge(&clipped, axis, &bound, keep_greater);
        if clipped.is_empty() {
            break;
        }
    }
    clipped
}

fn clip_polygon_edge(
    polygon: &[[Rat; 2]],
    axis: usize,
    bound: &Rat,
    keep_greater: bool,
) -> Vec<[Rat; 2]> {
    if polygon.is_empty() {
        return Vec::new();
    }
    let inside = |point: &[Rat; 2]| {
        if keep_greater {
            point[axis] >= *bound
        } else {
            point[axis] <= *bound
        }
    };
    let intersection = |first: &[Rat; 2], second: &[Rat; 2]| {
        let delta = &second[axis] - &first[axis];
        if delta.is_zero() {
            return first.clone();
        }
        let parameter = (bound - &first[axis]) / delta;
        [
            &first[0] + parameter.clone() * (&second[0] - &first[0]),
            &first[1] + parameter * (&second[1] - &first[1]),
        ]
    };
    let mut result = Vec::new();
    let mut previous = polygon.last().expect("nonempty polygon");
    let mut previous_inside = inside(previous);
    for current in polygon {
        let current_inside = inside(current);
        match (previous_inside, current_inside) {
            (true, true) => result.push(current.clone()),
            (true, false) => result.push(intersection(previous, current)),
            (false, true) => {
                result.push(intersection(previous, current));
                result.push(current.clone());
            }
            (false, false) => {}
        }
        previous = current;
        previous_inside = current_inside;
    }
    result
}

fn polygon_area(points: &[[Rat; 2]]) -> Rat {
    if points.len() < 3 {
        return Rat::zero();
    }
    let doubled = (0..points.len()).fold(Rat::zero(), |sum, index| {
        let next = (index + 1) % points.len();
        sum + &points[index][0] * &points[next][1] - &points[next][0] * &points[index][1]
    });
    if doubled.is_negative() {
        -doubled / Rat::from_integer(2.into())
    } else {
        doubled / Rat::from_integer(2.into())
    }
}

fn clip_segment_parameter_to_cell(
    start: &[Rat; 2],
    end: &[Rat; 2],
    cell: &ExactCell,
) -> Option<(Rat, Rat)> {
    let mut lower = Rat::zero();
    let mut upper = Rat::one();
    for axis in 0..2 {
        let delta = &end[axis] - &start[axis];
        if delta.is_zero() {
            if start[axis] < cell.lower[axis] || start[axis] > cell.upper[axis] {
                return None;
            }
            continue;
        }
        let mut first = (&cell.lower[axis] - &start[axis]) / &delta;
        let mut second = (&cell.upper[axis] - &start[axis]) / &delta;
        if first > second {
            std::mem::swap(&mut first, &mut second);
        }
        lower = std::cmp::max(lower, first);
        upper = std::cmp::min(upper, second);
        if lower > upper {
            return None;
        }
    }
    Some((lower, upper))
}
