//! Raw optical recovery as a material-founded extension of [`super`] source incidence.
//!
//! This owner never receives text, a symbol table, an equation name, or authored layout links.
//! Exact raster components supply the situated grains. The resident card classifies the complete
//! unordered centre-pair population at a material-derived aperture. Returned mathematical roles
//! remain receiver candidates, so a mark can lawfully inhabit several ambiguity alternatives.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    cuda_refine::{CudaRefineExecutor, DeviceContactPassage},
    image::{ExactRaster, ExactRgb},
};
use serde::{Deserialize, Serialize};

use super::{
    admit_raster_components, correspond, correspondence_demand, derive_raster_fiber,
    raster_component_admission_demand, raster_demand, ArtifactIdentity, ExactExtent, PlacedCarrier,
    Rat, SourceLayoutError, SourceLayoutWorkCover,
};

const SCHEMA: &str = "soma-life.raw-optical-mathematical-passage.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct OpticalBounds {
    pub left: i64,
    pub top: i64,
    pub right: i64,
    pub bottom: i64,
}

impl OpticalBounds {
    fn width(self) -> i64 {
        self.right - self.left
    }
    fn height(self) -> i64 {
        self.bottom - self.top
    }
    fn centre_x_twice(self) -> i64 {
        self.left + self.right
    }
    fn centre_y_twice(self) -> i64 {
        self.top + self.bottom
    }
    fn horizontal_overlap(self, other: Self) -> bool {
        self.left < other.right && other.left < self.right
    }
    fn vertical_overlap(self, other: Self) -> bool {
        self.top < other.bottom && other.top < self.bottom
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalComponent {
    pub address: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub bounds: OpticalBounds,
    pub four_connected_fibre: Vec<String>,
    pub region: u32,
    pub baseline_component: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum OpticalRelationKind {
    Proximity,
    BaselineCandidate,
    ReadingOrderAlternative,
    SuperscriptAttachmentCandidate,
    SubscriptAttachmentCandidate,
    FractionNumeratorCandidate,
    FractionDenominatorCandidate,
    RadicalEnclosureCandidate,
    DelimiterCandidate,
    MatrixRowCandidate,
    MatrixColumnCandidate,
    AlignmentRegionCandidate,
    DiagramIncidenceCandidate,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct OpticalRelation {
    pub from: u32,
    pub to: u32,
    pub kind: OpticalRelationKind,
    pub device_contact_class: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct AmbiguityAlternative {
    pub from: u32,
    pub to: u32,
    pub kind: OpticalRelationKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AmbiguityFibre {
    pub subject: String,
    pub alternatives: Vec<AmbiguityAlternative>,
    pub complete_within_exact_box_receiver: bool,
    pub symbol_identity_open_outside_receiver: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalRegion {
    pub ordinal: u32,
    pub component_ordinals: Vec<u32>,
    pub bounds: OpticalBounds,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOpticalConsequence {
    pub terms: Vec<u32>,
    pub factor_passages: Vec<u32>,
    pub variable_candidates: Vec<u32>,
    pub index_passages: Vec<u32>,
    pub numerator_containment: Vec<u32>,
    pub denominator_containment: Vec<u32>,
    pub delimiter_passages: Vec<u32>,
    pub radical_passages: Vec<u32>,
    pub matrix_and_alignment_passages: Vec<u32>,
    pub diagram_passages: Vec<u32>,
    /// Every relation retains both occurrence boundaries. Reversal is lineage transport and does
    /// not assert that a presented mathematical operation is invertible.
    pub inverse_transport: Vec<[u32; 2]>,
    /// Indices into the inherited optical testimony bound to this native occurrence.
    pub glyph_identity_faces: Vec<u32>,
    pub unit_identity_obstruction: String,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalRecoveryDemand {
    pub raster_sample_visits: u128,
    pub exact_component_pair_comparisons: u128,
    pub correspondence_pair_aperture: u128,
    pub predicted_gpu_launches: u64,
    pub predicted_gpu_synchronizations: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalWorkReceipt {
    pub demand: OpticalRecoveryDemand,
    pub returned_relation_population: u64,
    pub returned_fibre_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceOpticalReceipt {
    pub device_name: String,
    pub aperture_twice_pixels: u64,
    pub contact_classes: [u64; 3],
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub cpu_semantic_fallback: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalPassage {
    pub schema: String,
    pub truth_status: String,
    pub occurrence: String,
    pub source_octets: u64,
    pub source_sha256: String,
    pub width: u32,
    pub height: u32,
    pub components: Vec<OpticalComponent>,
    pub regions: Vec<OpticalRegion>,
    pub relations: Vec<OpticalRelation>,
    pub ambiguity_fibres: Vec<AmbiguityFibre>,
    pub native_consequence: NativeOpticalConsequence,
    pub glyph_testimony: Option<OpticalGlyphTestimony>,
    pub work: OpticalWorkReceipt,
    pub device: DeviceOpticalReceipt,
    pub productive_transcript_present: bool,
    pub productive_text_layer_present: bool,
    pub productive_anchor_labels_present: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExteriorOpticalGlyph {
    pub ordinal: u32,
    pub utf8_face: String,
    pub bounds: OpticalBounds,
    pub page: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalGlyphBinding {
    pub glyph_ordinal: u32,
    pub component_candidates: Vec<u32>,
    pub region_candidates: Vec<u32>,
    pub baseline_candidates: Vec<u32>,
    pub ambiguity_fibres: Vec<String>,
    pub unmatched: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalGlyphTestimony {
    pub organ: String,
    pub organ_version: String,
    pub glyphs: Vec<ExteriorOpticalGlyph>,
    pub bindings: Vec<OpticalGlyphBinding>,
    pub unmatched_glyphs: Vec<u32>,
    pub unmatched_components: Vec<u32>,
    pub plural_component_bindings: Vec<u32>,
    pub complete_overlap_fibre: bool,
    pub labels_route_spatial_law: bool,
}

/// One staged local difference. The continuing [`OpticalPassage`] is borrowed, never cloned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalAblationReturn {
    pub removed_relation: OpticalRelation,
    pub successor_relation_population: u64,
    pub successor_ambiguity_fibres: Vec<AmbiguityFibre>,
    pub successor_native_consequence: NativeOpticalConsequence,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalReceiverSignature {
    pub baseline: bool,
    pub scripts: bool,
    pub fraction: bool,
    pub radical_or_delimiter: bool,
    pub matrix_or_alignment: bool,
    pub diagram: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalControlComparison {
    pub common_native_receiver_faces: OpticalReceiverSignature,
    pub left_only_receiver_faces: OpticalReceiverSignature,
    pub right_only_receiver_faces: OpticalReceiverSignature,
    pub first_relation_separator: Option<OpticalRelation>,
    pub equal_receiver_signature_does_not_assert_source_equality: bool,
}

/// Recover from raw encoded bytes and exact pixels. `locator` is used only as exterior lineage and
/// is not retained in the native rest, so a filename cannot route the consequence.
pub fn recover_optical_passage(
    card: &mut CudaRefineExecutor,
    occurrence: impl Into<String>,
    locator: impl Into<String>,
    encoded_artifact: &[u8],
    raster: &ExactRaster,
    background: ExactRgb,
) -> Result<OpticalPassage, SourceLayoutError> {
    let occurrence = occurrence.into();
    let raster_work = raster_demand(raster)?;
    let fibre = derive_raster_fiber(
        occurrence.clone(),
        locator,
        encoded_artifact,
        raster,
        background,
        &SourceLayoutWorkCover::exactly(&raster_work),
    )?;
    let extent = ExactExtent::new(
        Rat::from_integer(raster.extent.width.into()),
        Rat::from_integer(raster.extent.height.into()),
    )?;
    let four_work = raster_component_admission_demand(&fibre.four_connected)?;
    let eight_work = raster_component_admission_demand(&fibre.eight_connected)?;
    let four = admit_raster_components(
        &fibre.four_connected,
        extent.clone(),
        &SourceLayoutWorkCover::exactly(&four_work),
    )?;
    let eight = admit_raster_components(
        &fibre.eight_connected,
        extent,
        &SourceLayoutWorkCover::exactly(&eight_work),
    )?;
    let correspondence_work = correspondence_demand(&four, &eight)?;
    let connectivity_fibre = correspond(
        &four,
        &eight,
        &SourceLayoutWorkCover::exactly(&correspondence_work),
    )?;

    let boxes = eight
        .occurrences
        .iter()
        .map(component_bounds)
        .collect::<Result<Vec<_>, _>>()?;
    let mut material_heights = boxes
        .iter()
        .map(|bounds| bounds.height())
        .collect::<Vec<_>>();
    material_heights.sort_unstable();
    let material_height = *material_heights
        .get(material_heights.len() / 2)
        .ok_or(SourceLayoutError::NoForeground)?;
    let aperture_twice = u64::try_from(material_height)
        .map_err(|_| SourceLayoutError::Extent)?
        .checked_mul(2)
        .ok_or(SourceLayoutError::Extent)?;
    let aperture_squared = aperture_twice
        .checked_mul(aperture_twice)
        .ok_or(SourceLayoutError::Extent)?;

    let vertex_count = boxes.len();
    let pair_count = vertex_count
        .checked_mul(vertex_count.saturating_sub(1))
        .and_then(|value| value.checked_div(2))
        .ok_or(SourceLayoutError::Extent)?;
    let mut coordinates = Vec::with_capacity(vertex_count * 3);
    for bounds in &boxes {
        coordinates.extend_from_slice(&[bounds.centre_x_twice(), bounds.centre_y_twice(), 0]);
    }
    let mut task_left = Vec::with_capacity(pair_count);
    let mut task_right = Vec::with_capacity(pair_count);
    for left in 0..vertex_count {
        for right in left + 1..vertex_count {
            task_left.push(u32::try_from(left).map_err(|_| SourceLayoutError::Extent)?);
            task_right.push(u32::try_from(right).map_err(|_| SourceLayoutError::Extent)?);
        }
    }
    let device = card
        .contact_passage_on_device(
            &coordinates,
            &coordinates,
            &task_left,
            &task_right,
            &[],
            &[],
            aperture_squared,
        )
        .map_err(|error| SourceLayoutError::Device(error.to_string()))?;
    let device_name = card.device_name().to_owned();
    return_from_device(
        occurrence,
        encoded_artifact,
        raster,
        &fibre.artifact,
        &eight.occurrences,
        &connectivity_fibre.right_candidates,
        boxes,
        task_left,
        task_right,
        device,
        aperture_twice,
        &device_name,
        raster_work.sample_visits,
        correspondence_work.pair_visits,
    )
}

#[allow(clippy::too_many_arguments)]
fn return_from_device(
    occurrence: String,
    encoded_artifact: &[u8],
    raster: &ExactRaster,
    artifact: &ArtifactIdentity,
    source_components: &[PlacedCarrier],
    connectivity_candidates: &BTreeMap<String, BTreeSet<String>>,
    boxes: Vec<OpticalBounds>,
    task_left: Vec<u32>,
    task_right: Vec<u32>,
    device: DeviceContactPassage,
    aperture_twice: u64,
    device_name: &str,
    sample_visits: u128,
    correspondence_pair_aperture: u128,
) -> Result<OpticalPassage, SourceLayoutError> {
    if device.contact_classes.len() != task_left.len() {
        return Err(SourceLayoutError::OpticalDeviceShape);
    }
    let mut relation_set = BTreeSet::new();
    for (at, class) in device.contact_classes.iter().copied().enumerate() {
        if class == 0 {
            continue;
        }
        let a = task_left[at];
        let b = task_right[at];
        let a_box = boxes[a as usize];
        let b_box = boxes[b as usize];
        insert_relation(
            &mut relation_set,
            a,
            b,
            OpticalRelationKind::Proximity,
            class,
        );

        let (earlier, later, earlier_box, later_box) =
            if a_box.centre_x_twice() <= b_box.centre_x_twice() {
                (a, b, a_box, b_box)
            } else {
                (b, a, b_box, a_box)
            };
        if earlier_box.vertical_overlap(later_box) {
            for kind in [
                OpticalRelationKind::BaselineCandidate,
                OpticalRelationKind::ReadingOrderAlternative,
                OpticalRelationKind::MatrixRowCandidate,
            ] {
                insert_relation(&mut relation_set, earlier, later, kind, class);
            }
        }
        if earlier_box.horizontal_overlap(later_box) {
            let (above, below) = if earlier_box.centre_y_twice() <= later_box.centre_y_twice() {
                (earlier, later)
            } else {
                (later, earlier)
            };
            for kind in [
                OpticalRelationKind::MatrixColumnCandidate,
                OpticalRelationKind::AlignmentRegionCandidate,
            ] {
                insert_relation(&mut relation_set, above, below, kind, class);
            }
        }
        if later_box.height() < earlier_box.height() {
            let kind = if later_box.centre_y_twice() < earlier_box.centre_y_twice() {
                OpticalRelationKind::SuperscriptAttachmentCandidate
            } else if later_box.centre_y_twice() > earlier_box.centre_y_twice() {
                OpticalRelationKind::SubscriptAttachmentCandidate
            } else {
                OpticalRelationKind::BaselineCandidate
            };
            insert_relation(&mut relation_set, earlier, later, kind, class);
        }
        for (frame, member, frame_box, member_box) in [(a, b, a_box, b_box), (b, a, b_box, a_box)] {
            if frame_box.width() > frame_box.height() && frame_box.horizontal_overlap(member_box) {
                let kind = if member_box.centre_y_twice() < frame_box.centre_y_twice() {
                    OpticalRelationKind::FractionNumeratorCandidate
                } else {
                    OpticalRelationKind::FractionDenominatorCandidate
                };
                insert_relation(&mut relation_set, frame, member, kind, class);
            }
            if frame_box.height() > frame_box.width() && frame_box.vertical_overlap(member_box) {
                insert_relation(
                    &mut relation_set,
                    frame,
                    member,
                    OpticalRelationKind::DelimiterCandidate,
                    class,
                );
                if frame_box.left <= member_box.left {
                    insert_relation(
                        &mut relation_set,
                        frame,
                        member,
                        OpticalRelationKind::RadicalEnclosureCandidate,
                        class,
                    );
                }
            }
            if frame_box.width() >= member_box.width().saturating_mul(2)
                || frame_box.height() >= member_box.height().saturating_mul(2)
            {
                insert_relation(
                    &mut relation_set,
                    frame,
                    member,
                    OpticalRelationKind::DiagramIncidenceCandidate,
                    class,
                );
            }
        }
    }
    let relations = relation_set.into_iter().collect::<Vec<_>>();
    let proximity = relation_edges(&relations, OpticalRelationKind::Proximity);
    let baselines = relation_edges(&relations, OpticalRelationKind::BaselineCandidate);
    let region_labels = connected_labels(boxes.len(), &proximity)?;
    let baseline_labels = connected_labels(boxes.len(), &baselines)?;
    let components = source_components
        .iter()
        .zip(&boxes)
        .enumerate()
        .map(|(at, (component, bounds))| OpticalComponent {
            address: component.address.clone(),
            payload_sha256: component.payload_sha256.clone(),
            payload_octets: component.payload_octets,
            bounds: *bounds,
            four_connected_fibre: connectivity_candidates
                .get(&component.address)
                .map(|set| set.iter().cloned().collect())
                .unwrap_or_default(),
            region: region_labels[at],
            baseline_component: baseline_labels[at],
        })
        .collect::<Vec<_>>();
    let regions = regions(&components)?;
    let ambiguity_fibres = ambiguity_fibres(&relations);
    let native_consequence = native_consequence(components.len(), &relations);
    let mut contact_classes = [0_u64; 3];
    for class in &device.contact_classes {
        let slot = usize::from(*class);
        if slot >= contact_classes.len() {
            return Err(SourceLayoutError::OpticalDeviceShape);
        }
        contact_classes[slot] += 1;
    }
    let demand = OpticalRecoveryDemand {
        raster_sample_visits: sample_visits,
        exact_component_pair_comparisons: task_left.len() as u128,
        correspondence_pair_aperture,
        predicted_gpu_launches: u64::from(!task_left.is_empty()),
        predicted_gpu_synchronizations: u64::from(!task_left.is_empty()),
    };
    Ok(OpticalPassage {
        schema: SCHEMA.to_owned(),
        truth_status: "implemented-exact".to_owned(),
        occurrence,
        source_octets: u64::try_from(encoded_artifact.len())
            .map_err(|_| SourceLayoutError::Extent)?,
        source_sha256: artifact.sha256.clone(),
        width: raster.extent.width,
        height: raster.extent.height,
        work: OpticalWorkReceipt {
            demand,
            returned_relation_population: relations.len() as u64,
            returned_fibre_population: ambiguity_fibres.len() as u64,
        },
        components,
        regions,
        relations,
        ambiguity_fibres,
        native_consequence,
        glyph_testimony: None,
        device: DeviceOpticalReceipt {
            device_name: device_name.to_owned(),
            aperture_twice_pixels: aperture_twice,
            contact_classes,
            launches: device.launches,
            synchronizations: device.synchronizations,
            host_ingress_octets: device.host_ingress_octets,
            host_egress_octets: device.host_egress_octets,
            resident_octets: device.resident_octets,
            cpu_semantic_fallback: false,
        },
        productive_transcript_present: false,
        productive_text_layer_present: false,
        productive_anchor_labels_present: false,
    })
}

fn insert_relation(
    relations: &mut BTreeSet<OpticalRelation>,
    from: u32,
    to: u32,
    kind: OpticalRelationKind,
    device_contact_class: u8,
) {
    relations.insert(OpticalRelation {
        from,
        to,
        kind,
        device_contact_class,
    });
}

fn component_bounds(component: &PlacedCarrier) -> Result<OpticalBounds, SourceLayoutError> {
    Ok(OpticalBounds {
        left: integer_rat(component.bounds.left())?,
        top: integer_rat(component.bounds.top())?,
        right: integer_rat(component.bounds.right())?,
        bottom: integer_rat(component.bounds.bottom())?,
    })
}

fn integer_rat(value: &Rat) -> Result<i64, SourceLayoutError> {
    if value.denom() != &1.into() {
        return Err(SourceLayoutError::OpticalCoordinateNotIntegral);
    }
    value
        .numer()
        .to_string()
        .parse::<i64>()
        .map_err(|_| SourceLayoutError::Extent)
}

fn relation_edges(relations: &[OpticalRelation], kind: OpticalRelationKind) -> Vec<(u32, u32)> {
    relations
        .iter()
        .filter(|relation| relation.kind == kind)
        .map(|relation| (relation.from, relation.to))
        .collect()
}

fn connected_labels(
    population: usize,
    edges: &[(u32, u32)],
) -> Result<Vec<u32>, SourceLayoutError> {
    let mut parent = (0..population).collect::<Vec<_>>();
    fn root(parent: &mut [usize], mut at: usize) -> usize {
        while parent[at] != at {
            parent[at] = parent[parent[at]];
            at = parent[at];
        }
        at
    }
    for (left, right) in edges {
        let a = root(&mut parent, *left as usize);
        let b = root(&mut parent, *right as usize);
        if a != b {
            let joined = a.min(b);
            parent[a] = joined;
            parent[b] = joined;
        }
    }
    let mut labels = BTreeMap::<usize, u32>::new();
    let mut next = 0_u32;
    (0..population)
        .map(|at| {
            let key = root(&mut parent, at);
            Ok(*labels.entry(key).or_insert_with(|| {
                let label = next;
                next += 1;
                label
            }))
        })
        .collect()
}

fn regions(components: &[OpticalComponent]) -> Result<Vec<OpticalRegion>, SourceLayoutError> {
    let mut members = BTreeMap::<u32, Vec<u32>>::new();
    for (at, component) in components.iter().enumerate() {
        members
            .entry(component.region)
            .or_default()
            .push(u32::try_from(at).map_err(|_| SourceLayoutError::Extent)?);
    }
    members
        .into_iter()
        .map(|(ordinal, component_ordinals)| {
            let first = components[component_ordinals[0] as usize].bounds;
            let bounds = component_ordinals.iter().skip(1).fold(first, |bounds, at| {
                let next = components[*at as usize].bounds;
                OpticalBounds {
                    left: bounds.left.min(next.left),
                    top: bounds.top.min(next.top),
                    right: bounds.right.max(next.right),
                    bottom: bounds.bottom.max(next.bottom),
                }
            });
            Ok(OpticalRegion {
                ordinal,
                component_ordinals,
                bounds,
            })
        })
        .collect()
}

fn ambiguity_fibres(relations: &[OpticalRelation]) -> Vec<AmbiguityFibre> {
    let mut alternatives = BTreeMap::<(u32, u32), BTreeSet<OpticalRelationKind>>::new();
    for relation in relations {
        if relation.kind != OpticalRelationKind::Proximity {
            alternatives
                .entry((relation.from, relation.to))
                .or_default()
                .insert(relation.kind);
        }
    }
    alternatives
        .into_iter()
        .filter(|(_, kinds)| kinds.len() > 1)
        .map(|((from, to), kinds)| AmbiguityFibre {
            subject: format!("optical-pair:{from}:{to}"),
            alternatives: kinds
                .into_iter()
                .map(|kind| AmbiguityAlternative { from, to, kind })
                .collect(),
            complete_within_exact_box_receiver: true,
            symbol_identity_open_outside_receiver: true,
        })
        .collect()
}

fn native_consequence(
    component_population: usize,
    relations: &[OpticalRelation],
) -> NativeOpticalConsequence {
    let indices = |kinds: &[OpticalRelationKind]| {
        relations
            .iter()
            .enumerate()
            .filter(|(_, relation)| kinds.contains(&relation.kind))
            .map(|(at, _)| at as u32)
            .collect::<Vec<_>>()
    };
    let structural = relations
        .iter()
        .filter(|relation| {
            !matches!(
                relation.kind,
                OpticalRelationKind::Proximity
                    | OpticalRelationKind::BaselineCandidate
                    | OpticalRelationKind::ReadingOrderAlternative
            )
        })
        .flat_map(|relation| [relation.from, relation.to])
        .collect::<BTreeSet<_>>();
    NativeOpticalConsequence {
        terms: (0..component_population as u32).collect(),
        factor_passages: indices(&[OpticalRelationKind::BaselineCandidate,OpticalRelationKind::ReadingOrderAlternative]),
        variable_candidates: (0..component_population as u32).filter(|at| !structural.contains(at)).collect(),
        index_passages: indices(&[OpticalRelationKind::SuperscriptAttachmentCandidate,OpticalRelationKind::SubscriptAttachmentCandidate]),
        numerator_containment: indices(&[OpticalRelationKind::FractionNumeratorCandidate]),
        denominator_containment: indices(&[OpticalRelationKind::FractionDenominatorCandidate]),
        delimiter_passages: indices(&[OpticalRelationKind::DelimiterCandidate]),
        radical_passages: indices(&[OpticalRelationKind::RadicalEnclosureCandidate]),
        matrix_and_alignment_passages: indices(&[OpticalRelationKind::MatrixRowCandidate,
            OpticalRelationKind::MatrixColumnCandidate,OpticalRelationKind::AlignmentRegionCandidate]),
        diagram_passages: indices(&[OpticalRelationKind::DiagramIncidenceCandidate]),
        inverse_transport: relations.iter().map(|relation| [relation.to,relation.from]).collect(),
        glyph_identity_faces: Vec::new(),
        unit_identity_obstruction: "exact placement does not select unit identity without a symbol/morphology receiver".to_owned(),
        open_exterior: vec![
            "glyph identity and same-layout/different-operator separation require an inherited optical morphology absent from mathematical_source".to_owned(),
            "radical versus delimiter and diagram versus decoration remain retained alternatives".to_owned(),
            "a richer successor family can reopen every exact-box grouping".to_owned(),
        ],
    }
}

/// Bind an inherited exterior optical face to every overlapping raw component. Labels never
/// select the spatial law: plural overlaps, unmatched glyphs/components, and ambiguity fibres are
/// returned together.
pub fn bind_optical_glyph_testimony(
    passage: &mut OpticalPassage,
    organ: impl Into<String>,
    organ_version: impl Into<String>,
    glyphs: Vec<ExteriorOpticalGlyph>,
) -> Result<(), SourceLayoutError> {
    if passage.glyph_testimony.is_some() {
        return Err(SourceLayoutError::OpticalGlyphTestimonyAlreadyBound);
    }
    let mut matched_components = BTreeSet::new();
    let mut unmatched_glyphs = Vec::new();
    let mut plural_component_bindings = Vec::new();
    let mut bindings = Vec::with_capacity(glyphs.len());
    for glyph in &glyphs {
        if glyph.bounds.left > glyph.bounds.right
            || glyph.bounds.top > glyph.bounds.bottom
            || glyph.bounds.left < 0
            || glyph.bounds.top < 0
            || glyph.bounds.right > i64::from(passage.width)
            || glyph.bounds.bottom > i64::from(passage.height)
        {
            return Err(SourceLayoutError::OpticalGlyphOutsideExtent(glyph.ordinal));
        }
        let component_candidates = passage
            .components
            .iter()
            .enumerate()
            .filter(|(_, component)| boxes_overlap(component.bounds, glyph.bounds))
            .map(|(at, _)| u32::try_from(at).map_err(|_| SourceLayoutError::Extent))
            .collect::<Result<Vec<_>, _>>()?;
        for component in &component_candidates {
            matched_components.insert(*component);
        }
        if component_candidates.is_empty() {
            unmatched_glyphs.push(glyph.ordinal);
        }
        if component_candidates.len() > 1 {
            plural_component_bindings.push(glyph.ordinal);
        }
        let region_candidates = component_candidates
            .iter()
            .map(|at| passage.components[*at as usize].region)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let baseline_candidates = component_candidates
            .iter()
            .map(|at| passage.components[*at as usize].baseline_component)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let ambiguity_fibres = passage
            .ambiguity_fibres
            .iter()
            .filter(|fibre| {
                fibre.alternatives.iter().any(|alternative| {
                    component_candidates.contains(&alternative.from)
                        || component_candidates.contains(&alternative.to)
                })
            })
            .map(|fibre| fibre.subject.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        bindings.push(OpticalGlyphBinding {
            glyph_ordinal: glyph.ordinal,
            unmatched: component_candidates.is_empty(),
            component_candidates,
            region_candidates,
            baseline_candidates,
            ambiguity_fibres,
        });
    }
    let unmatched_components = (0..passage.components.len() as u32)
        .filter(|at| !matched_components.contains(at))
        .collect();
    passage.native_consequence.glyph_identity_faces =
        glyphs.iter().map(|glyph| glyph.ordinal).collect();
    passage.native_consequence.open_exterior.retain(|boundary| {
        !boundary.starts_with("glyph identity and same-layout/different-operator")
    });
    passage.native_consequence.open_exterior.push(
        "glyph alternatives beyond the inherited makebox receiver remain open".to_owned(),
    );
    passage.glyph_testimony = Some(OpticalGlyphTestimony {
        organ: organ.into(),
        organ_version: organ_version.into(),
        glyphs,
        bindings,
        unmatched_glyphs,
        unmatched_components,
        plural_component_bindings,
        complete_overlap_fibre: true,
        labels_route_spatial_law: false,
    });
    Ok(())
}

fn boxes_overlap(left: OpticalBounds, right: OpticalBounds) -> bool {
    left.left < right.right
        && right.left < left.right
        && left.top < right.bottom
        && right.top < left.bottom
}

fn signature(passage: &OpticalPassage) -> OpticalReceiverSignature {
    let has = |kinds: &[OpticalRelationKind]| {
        passage
            .relations
            .iter()
            .any(|relation| kinds.contains(&relation.kind))
    };
    OpticalReceiverSignature {
        baseline: has(&[OpticalRelationKind::BaselineCandidate]),
        scripts: has(&[
            OpticalRelationKind::SuperscriptAttachmentCandidate,
            OpticalRelationKind::SubscriptAttachmentCandidate,
        ]),
        fraction: has(&[
            OpticalRelationKind::FractionNumeratorCandidate,
            OpticalRelationKind::FractionDenominatorCandidate,
        ]),
        radical_or_delimiter: has(&[
            OpticalRelationKind::RadicalEnclosureCandidate,
            OpticalRelationKind::DelimiterCandidate,
        ]),
        matrix_or_alignment: has(&[
            OpticalRelationKind::MatrixRowCandidate,
            OpticalRelationKind::MatrixColumnCandidate,
            OpticalRelationKind::AlignmentRegionCandidate,
        ]),
        diagram: has(&[OpticalRelationKind::DiagramIncidenceCandidate]),
    }
}

pub fn compare_optical_controls(
    left: &OpticalPassage,
    right: &OpticalPassage,
) -> OpticalControlComparison {
    let a = signature(left);
    let b = signature(right);
    let apply = |op: fn(bool, bool) -> bool| OpticalReceiverSignature {
        baseline: op(a.baseline, b.baseline),
        scripts: op(a.scripts, b.scripts),
        fraction: op(a.fraction, b.fraction),
        radical_or_delimiter: op(a.radical_or_delimiter, b.radical_or_delimiter),
        matrix_or_alignment: op(a.matrix_or_alignment, b.matrix_or_alignment),
        diagram: op(a.diagram, b.diagram),
    };
    fn common(a: bool, b: bool) -> bool {
        a && b
    }
    fn left_only(a: bool, b: bool) -> bool {
        a && !b
    }
    fn right_only(a: bool, b: bool) -> bool {
        b && !a
    }
    let left_relations = left.relations.iter().cloned().collect::<BTreeSet<_>>();
    let right_relations = right.relations.iter().cloned().collect::<BTreeSet<_>>();
    OpticalControlComparison {
        common_native_receiver_faces: apply(common),
        left_only_receiver_faces: apply(left_only),
        right_only_receiver_faces: apply(right_only),
        first_relation_separator: left_relations
            .symmetric_difference(&right_relations)
            .next()
            .cloned(),
        equal_receiver_signature_does_not_assert_source_equality: true,
    }
}

/// Target one returned relation after the native consequence is frozen. The predecessor passage
/// is left owned by the caller; the ablated difference is another local return, not a rollback
/// clone of the continuing ecology.
pub fn ablate_optical_relation(
    passage: &OpticalPassage,
    relation_ordinal: usize,
) -> Result<OpticalAblationReturn, SourceLayoutError> {
    if relation_ordinal >= passage.relations.len() {
        return Err(SourceLayoutError::Extent);
    }
    let removed_relation = passage.relations[relation_ordinal].clone();
    let successor_relations = passage
        .relations
        .iter()
        .enumerate()
        .filter(|(at, _)| *at != relation_ordinal)
        .map(|(_, relation)| relation.clone())
        .collect::<Vec<_>>();
    let mut successor_native_consequence =
        native_consequence(passage.components.len(), &successor_relations);
    successor_native_consequence.glyph_identity_faces =
        passage.native_consequence.glyph_identity_faces.clone();
    Ok(OpticalAblationReturn {
        removed_relation,
        successor_relation_population: successor_relations.len() as u64,
        successor_ambiguity_fibres: ambiguity_fibres(&successor_relations),
        successor_native_consequence,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plural_spatial_roles_remain_one_complete_declared_fibre() {
        let relations = vec![
            OpticalRelation {
                from: 0,
                to: 1,
                kind: OpticalRelationKind::Proximity,
                device_contact_class: 1,
            },
            OpticalRelation {
                from: 0,
                to: 1,
                kind: OpticalRelationKind::DelimiterCandidate,
                device_contact_class: 1,
            },
            OpticalRelation {
                from: 0,
                to: 1,
                kind: OpticalRelationKind::RadicalEnclosureCandidate,
                device_contact_class: 1,
            },
        ];
        let fibres = ambiguity_fibres(&relations);
        assert_eq!(fibres.len(), 1);
        assert_eq!(fibres[0].alternatives.len(), 2);
        assert!(fibres[0].complete_within_exact_box_receiver);
        assert!(fibres[0].symbol_identity_open_outside_receiver);
    }

    #[test]
    fn line_and_region_labels_are_derived_from_returned_edges() {
        let labels = connected_labels(5, &[(0, 1), (1, 2), (3, 4)]).unwrap();
        assert_eq!(labels[0], labels[2]);
        assert_eq!(labels[3], labels[4]);
        assert_ne!(labels[0], labels[3]);
    }
}
