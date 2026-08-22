//! **The whole text tower as ONE streamed resident circulation** — the site that replaces the
//! per-layer apparatus foreman of `phoenix/conduct.rs` for Deed H4.
//!
//! The diagram is unchanged: every layer is founded by `phoenix/tower.rs`, from the same source
//! testimony, at the same grain, under the same declared quotient chart. What changes is
//! everything around it, and every change is one of H0's measured findings:
//!
//! ```text
//!   H0 measured                          this site
//!   ----------------------------------   --------------------------------------------------
//!   one exterior occurrence rebuilt per  ONE authenticated native-rest occurrence, retained
//!   layer (apparatus re-read and hashed)  before the deed and reused across all segments
//!
//!   per-region SHA-256 of every octet    NONE in the circulation. The container's identity
//!   read, every layer, every run         (device/inode/size/mtime/ctime) is taken before and
//!   (~184 ms of the 296 ms gap)          verified after; the whole-content digest is REUSED
//!                                        from the committed manifest with its date stated
//!
//!   9,416 cuMemAlloc + 9,416 cuMemFree   three pooled slots, three allocations, reused
//!
//!   2,112 cuCtxSynchronize (one per      two synchronizations of a MOUNT stream per segment,
//!   mount kernel), each draining the     which is the mouth's own host round trip and nothing
//!   whole context                        else; the conducting stream never waits
//!
//!   1,745 synchronous copies, 0 ns of    one asynchronous copy per region on a copy stream,
//!   them concurrent with any kernel      ordered against the deed that last read the slot by a
//!                                        device event, so a refill crosses while a deed conducts
//!
//!   43 launches, 43 synchronizations     43 launches, ONE terminal synchronization
//! ```
//!
//! **No CPU semantic inspection between source layers**, and it is structural rather than
//! promised: the loop below holds a [`StreamedCirculation`], which has no accessor returning a
//! section, a census slot or a terminal; every deed's return is asked for **after** the terminal
//! synchronization, from a population the loop only ever pushed onto. The driver asserts the
//! surface's own `section_read_outs` and `egress_section_octets` did not move across the loop.
//!
//! This is a site, not a library owner: it binds one source instance and declares no operation.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::fs::FileExt;
use std::rc::Rc;
use std::time::Instant;

use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::causal::EventId;
use crate::embedding_fiber::ResidentReadout;
use crate::exact_work::ExactWork;
use crate::front_passage::{
    CompiledPassage, DeedReceiver, EnteringRows, FrontPassage, FrontPassageObstruction,
    MaterialAdmission, MountedPopulation, PooledMaterialAuxiliary, ResidentMaterial,
    ResourceObstruction, SealedMidpointQuotient, factored_seals,
};
use crate::interaction::OccurrencePort;
use crate::resident_section::{
    Dyadic, ResidentGrain, ResidentSection, ResidentSurface, SeriesAperture, TransferCensus,
};
use crate::source_occurrence::{OccurrenceWitness, RegionIdentity};
use crate::streamed_standing::{
    GraphKey, SlotShape, StagedRegion, StreamedCensus, StreamedCirculation,
};

use super::tower::{self, Entry, Intervention, KvRole, Species};

/// The one place in the streamed tower at which a matched sibling is changed.
///
/// This is an apparatus-facing site declaration, not an operation taxonomy.  The tower still
/// owns the intervention law; the circulation only decides which layer receives the caller's
/// occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterventionSite {
    /// The W2/W3 base deed: no intervention is enacted.
    Nowhere,
    /// Enact the same intervention at every layer graph.
    EveryLayer,
    /// Enact it at one layer graph only.
    Layer(usize),
    /// Enact it at the final normalization/output graph only.
    Final,
}

#[cfg(test)]
mod tests {
    use super::{ApparatusCensus, tower_admission_receipt};
    use crate::front_passage::DeedAdmission;
    use crate::resident_section::TransferCensus;
    use crate::streamed_standing::StreamedCensus;

    #[test]
    fn tower_admission_receipt_binds_the_actual_serialized_admissions() {
        let admission = DeedAdmission {
            semantic: Vec::new(),
            apparatus: Vec::new(),
            cited_material: None,
            free_octets_at_admission: 17,
        };
        let receipt = tower_admission_receipt(vec![admission.clone()]).expect("serializes");
        let expected = serde_json::to_string(&[admission]).expect("admission serialization");
        assert_eq!(receipt.serialized, expected);
        assert!(!receipt.identity.is_empty());
    }

    #[test]
    fn apparatus_census_type_keeps_overlay_window_separate() {
        let census = ApparatusCensus {
            resident_before: TransferCensus::default(),
            resident_after_tower: TransferCensus::default(),
            resident_after: TransferCensus {
                deed_launches: 1,
                ..TransferCensus::default()
            },
            overlay_before: Some(TransferCensus::default()),
            overlay_after: Some(TransferCensus {
                deed_launches: 1,
                ..TransferCensus::default()
            }),
            streamed: StreamedCensus {
                graph_launches: 1,
                terminal_synchronizations: 1,
                ..StreamedCensus::default()
            },
            tower_deed_launches: 1,
            total_deed_launches: 2,
            terminal_synchronizations: 1,
        };
        assert_eq!(census.tower_deed_launches + 1, census.total_deed_launches);
        assert!(census.overlay_before.is_some() && census.overlay_after.is_some());
    }
}

/// Short alias for callers which use the exterior site chart's name.
pub type Site = InterventionSite;

impl InterventionSite {
    fn applies_to_layer(self, layer: usize) -> bool {
        match self {
            Self::EveryLayer => true,
            Self::Layer(at) => at == layer,
            Self::Nowhere | Self::Final => false,
        }
    }

    fn applies_to_final(self) -> bool {
        matches!(self, Self::Final)
    }
}

/// Receiver declaration for the streamed circulation.  Terminal output is the historical W2/W3
/// receiver.  `Complete` additionally asks for all layer PLE/contact/layer-return faces; those
/// faces are copied only after the single terminal synchronization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiverOption {
    Terminal,
    Complete,
}

pub type CirculationReceiver = ReceiverOption;
pub type Receiver = ReceiverOption;

/// The three named layer returns retained by the complete receiver family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayerReceiverFaces {
    pub layer: usize,
    pub ple: Vec<(i64, i64)>,
    pub contact: Vec<(i64, i64)>,
    pub layer_return: Vec<(i64, i64)>,
}

pub type LayerFaces = LayerReceiverFaces;

/// Complete post-synchronization receiver return for one streamed tower.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverFaces {
    pub layers: Vec<LayerReceiverFaces>,
    pub final_normed: Vec<(i64, i64)>,
    pub potential: Vec<(i64, i64)>,
}

pub type CompleteFaces = ReceiverFaces;

/// The actual admissions of every bound deed in one tower, retained in launch order. The
/// serialized form and identity are derived from these returned admissions; no prediction or
/// reconstructed summary stands in for the admission the card used.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TowerAdmissionReceipt {
    pub deeds: Vec<crate::front_passage::DeedAdmission>,
    pub serialized: String,
    pub identity: String,
}

/// A non-double-counted apparatus window. `resident_*` are absolute surface censuses over the
/// tower; an optional overlay window is a separate nested deed, while `streamed` is the pooled
/// transport census. Consumers must not add the absolute windows as if they were deltas.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ApparatusCensus {
    pub resident_before: TransferCensus,
    pub resident_after_tower: TransferCensus,
    pub resident_after: TransferCensus,
    pub overlay_before: Option<TransferCensus>,
    pub overlay_after: Option<TransferCensus>,
    pub streamed: StreamedCensus,
    pub tower_deed_launches: u64,
    pub total_deed_launches: u64,
    pub terminal_synchronizations: u64,
}

#[path = "cultivation_overlay.rs"]
pub mod cultivation_overlay;
#[path = "streamed_cultivation.rs"]
pub mod streamed_cultivation;
use streamed_cultivation::{CirculationOutput, OverlayExecutionIdentity, digest_face};
pub use streamed_cultivation::{CultivatedCirculated, CultivationRequest};

/// The two pool slots the source layers alternate between, and the third the final deed uses.
pub const SLOTS: usize = 3;
pub const FINAL_SLOT: usize = SLOTS - 1;
/// The final boundary's own pinned slot, after the three the source layers alternate between.
pub const FINAL_PINNED: usize = SLOTS;

/// The one material-source face H4 needs.  The streamed circulation owns the transport and
/// tower laws; this trait owns only the exterior crossing which supplies them.  In particular,
/// a source is not a tensor container in the circulation: it is a stable file extent, exact
/// region testimony, row/word access, one occurrence witness, and a post-deed drift check.
pub trait MaterialSource {
    fn file(&self) -> Result<&std::fs::File, String>;
    fn file_octets(&self) -> Result<u64, String>;
    fn region(&self, population: &str) -> Result<RegionIdentity, String>;
    fn staged(&self, population: &str) -> Result<StagedRegion, String>;
    fn rows(
        &mut self,
        population: &str,
        from: usize,
        count: usize,
    ) -> Result<(Vec<u16>, usize), String>;
    fn occurrence(&self) -> &dyn OccurrenceWitness;
    fn source_identity(&self) -> String;
    fn verify_stable(&self) -> Result<(), String>;
}

/// the header, whose own digest is taken here. The reuse is stated on the receipt; a caller that
/// wants it re-taken passes `--digest-container`.
pub const COMMITTED_CONTENT_SHA256: &str =
    "cfbd3d2f1cd71bd471c37fe2bf8546d5028d41e5736f64e1ca6c6b8893125503";
pub const COMMITTED_CONTENT_TAKEN: &str = "2026-08-19, Station B/C";

/// One segment's declaration: the regions it stages, the material names they mount as, and the
/// pool slot they land in. A segment boundary is the **pinned-staging refill**, which is the one
/// exterior I/O boundary in the circulation.
pub struct Segment {
    pub layer: Option<usize>,
    pub slot: usize,
    pub pinned: usize,
    pub regions: Vec<StagedRegion>,
    /// The material name each staged region mounts under, in the same order.
    pub names: Vec<String>,
    /// The region carrying the layer scalar, read as a host word and mounted nowhere.
    pub scalar: Option<StagedRegion>,
}

/// The header identity of one population, without a content digest.
fn region_of(source: &dyn MaterialSource, population: &str) -> Result<RegionIdentity, String> {
    source.region(population)
}

/// A staged region addresses the FILE, so it carries the payload base; a `RegionIdentity`
/// addresses the container's payload, so it does not. Conflating the two reads the wrong octets and
/// the deed still returns numbers — measured 2026-08-19, when it did: the tower conducted ten
/// layers on the wrong weights before an a-priori octave bound refused at layer 10.
fn staged_of(source: &dyn MaterialSource, population: &str) -> Result<StagedRegion, String> {
    source.staged(population)
}

/// **Every region the whole tower reads, declared from the container's header alone.** Nothing is
/// opened, nothing is digested, and this is what the one pre-deed native-rest occurrence carries.
pub fn header_regions(
    source: &dyn MaterialSource,
) -> Result<BTreeMap<String, RegionIdentity>, String> {
    let mut regions = BTreeMap::new();
    for layer in 0..tower::LAYERS {
        for name in tower::populations(layer) {
            regions.insert(name.clone(), region_of(source, &name)?);
        }
        let scalar = tower::named(layer, "layer_scalar");
        regions.insert(scalar.clone(), region_of(source, &scalar)?);
        // The layer's own slice of the per-layer model projection: the octet span read, named.
        let whole = source.region(tower::PLE_MODEL_PROJECTION)?;
        let dim = whole.shape[1];
        let mut slice = region_of(source, tower::PLE_MODEL_PROJECTION)?;
        slice.population = format!(
            "{} rows {}..{}",
            tower::PLE_MODEL_PROJECTION,
            tower::PLE_WIDTH * layer,
            tower::PLE_WIDTH * (layer + 1)
        );
        slice.shape = vec![tower::PLE_WIDTH, dim];
        slice.start += (tower::PLE_WIDTH * layer * dim * 2) as u64;
        slice.end = slice.start + (tower::PLE_WIDTH * dim * 2) as u64;
        regions.insert(slice.population.clone(), slice);
    }
    for name in [
        tower::PLE_MODEL_PROJECTION,
        tower::PLE_PROJECTION_NORM,
        tower::EMBED,
        tower::PLE_EMBED,
        tower::FINAL_NORM,
    ] {
        regions.insert(name.to_owned(), region_of(source, name)?);
    }
    Ok(regions)
}

/// The regions one layer's segment stages, **in the order `tower::mount_layer` mounts them**, so
/// the pooled mount and the per-deed mount name the same maps in the same order.
pub fn layer_segment(
    source: &dyn MaterialSource,
    layer: usize,
    slot: usize,
    pinned: usize,
) -> Result<Segment, String> {
    let mut regions = Vec::new();
    let mut names = Vec::new();
    for name in tower::populations(layer) {
        regions.push(staged_of(source, &name)?);
        names.push(name);
    }
    // The layer's 256 rows of the per-layer model projection, mounted under the whole tensor's name.
    let whole = source.staged(tower::PLE_MODEL_PROJECTION)?;
    let dim = whole.dim;
    regions.push(StagedRegion {
        population: format!(
            "{} rows {}..{}",
            tower::PLE_MODEL_PROJECTION,
            tower::PLE_WIDTH * layer,
            tower::PLE_WIDTH * (layer + 1)
        ),
        start: whole.start + (tower::PLE_WIDTH * layer * dim * 2) as u64,
        words: (tower::PLE_WIDTH * dim) as u32,
        dim,
    });
    names.push(tower::PLE_MODEL_PROJECTION.to_owned());
    regions.push(staged_of(source, tower::PLE_PROJECTION_NORM)?);
    names.push(tower::PLE_PROJECTION_NORM.to_owned());
    let scalar = staged_of(source, &tower::named(layer, "layer_scalar"))?;
    Ok(Segment {
        layer: Some(layer),
        slot,
        pinned,
        regions,
        names,
        scalar: Some(scalar),
    })
}

/// The final deed's segment: the final norm gain and the tied output table.
pub fn final_segment(
    source: &dyn MaterialSource,
    slot: usize,
    pinned: usize,
) -> Result<Segment, String> {
    let mut regions = Vec::new();
    let mut names = Vec::new();
    for name in [tower::FINAL_NORM, tower::EMBED] {
        regions.push(staged_of(source, name)?);
        names.push(name.to_owned());
    }
    Ok(Segment {
        layer: None,
        slot,
        pinned,
        regions,
        names,
        scalar: None,
    })
}

/// The pool slot shapes, from the segments alone: the widest layer decides both alternating slots,
/// and the final deed has its own. Every number is derived from the container's header.
pub fn slot_shapes(layers: &[Segment], last: &Segment) -> Vec<SlotShape> {
    let widest = |segments: &[&Segment]| -> (usize, usize, usize, usize) {
        let mut aligned = 0usize;
        let mut stored = 0usize;
        let mut mass = 0usize;
        let mut maps = 0usize;
        for segment in segments {
            aligned = aligned.max(
                segment
                    .regions
                    .iter()
                    .map(|r| r.words as usize * 8)
                    .sum::<usize>(),
            );
            stored = stored.max(
                segment
                    .regions
                    .iter()
                    .map(StagedRegion::octets)
                    .sum::<usize>(),
            );
            mass = mass.max(segment.regions.iter().map(|r| r.rows() * 16).sum::<usize>());
            maps = maps.max(segment.regions.len());
        }
        (aligned, stored, mass, 16 * maps)
    };
    let every: Vec<&Segment> = layers.iter().collect();
    let (aligned, stored, mass, scratch) = widest(&every);
    let (final_aligned, final_stored, final_mass, final_scratch) = widest(&[last]);
    vec![
        SlotShape {
            name: "pooled source standing, slot 0 (even source layers)".to_owned(),
            aligned_octets: aligned,
            stored_octets: stored,
            mass_octets: mass,
            scratch_octets: scratch,
        },
        SlotShape {
            name: "pooled source standing, slot 1 (odd source layers)".to_owned(),
            aligned_octets: aligned,
            stored_octets: stored,
            mass_octets: mass,
            scratch_octets: scratch,
        },
        SlotShape {
            name: "pooled source standing, slot 2 (the final boundary)".to_owned(),
            aligned_octets: final_aligned,
            stored_octets: final_stored,
            mass_octets: final_mass,
            scratch_octets: final_scratch,
        },
    ]
}

/// One pressure-resilient resident source slot, derived as the componentwise cover of the layer
/// and final slots. Reusing it removes copy overlap but changes no mounted population: its event
/// orders every refill after the preceding graph, and every region keeps the same source address
/// and exact mounted extent. This is the apparatus partition used by the productive runtime.
pub fn resident_window_slot_shape(layers: &[Segment], last: &Segment) -> Vec<SlotShape> {
    let plural = slot_shapes(layers, last);
    vec![SlotShape {
        name: "one reusable resident source slot covering every layer and final boundary"
            .to_owned(),
        aligned_octets: plural
            .iter()
            .map(|shape| shape.aligned_octets)
            .max()
            .unwrap_or(0),
        stored_octets: plural
            .iter()
            .map(|shape| shape.stored_octets)
            .max()
            .unwrap_or(0),
        mass_octets: plural
            .iter()
            .map(|shape| shape.mass_octets)
            .max()
            .unwrap_or(0),
        scratch_octets: plural
            .iter()
            .map(|shape| shape.scratch_octets)
            .max()
            .unwrap_or(0),
    }]
}

/// One layer's receipt in the circulation. Deliberately narrow: the faces a receiver reads are the
/// terminal ones, and the loop reads none of them.
pub struct SegmentReceipt {
    pub layer: Option<usize>,
    pub slot: usize,
    /// Maps staged, crossed and mounted in this segment.
    pub maps: usize,
    pub species: Option<Species>,
    pub role: Option<KvRole>,
    pub operations: usize,
    pub fronts: usize,
    pub graph_nodes: usize,
    pub graph_edges: usize,
    pub captured_launches: u64,
    pub seals_fused: usize,
    pub seals_refused: Vec<(EventId, String)>,
    pub quotients: usize,
    pub collapsed_width_sum: u128,
    pub collapsed_width_max: u64,
    pub collapsed_nonzero: u64,
    pub lineage_empty: bool,
    pub a_priori_held: bool,
    pub every_front_certified: bool,
    pub deed: ExactWork,
    pub material_resident_octets: u64,
    pub stage_wall_s: f64,
    pub mount_wall_s: f64,
    pub bind_wall_s: f64,
}

type BoundDeed<'chart> = (
    CompiledPassage<'chart>,
    TransferCensus,
    BTreeMap<&'chart str, EventId>,
    usize,
);

fn residency_pressure(obstruction: &FrontPassageObstruction) -> bool {
    matches!(
        obstruction,
        FrontPassageObstruction::Resource(ResourceObstruction::Apparatus { coordinate })
            if coordinate.name == "charged-resident-octets"
    )
}

/// Discharge one completed resident window. Every section read here was explicitly declared by
/// the receiver, and the function is called only after the conducting current was fenced. Layer
/// returns and shared K/V already crossed by ownership transfer and therefore survive passage
/// release without a host semantic copy.
#[allow(clippy::too_many_arguments)]
fn discharge_window<'chart>(
    deeds: &mut Vec<BoundDeed<'chart>>,
    receipts: &mut [SegmentReceipt],
    receiver_option: ReceiverOption,
    cultivation_present: bool,
    obstructions: &mut Vec<(usize, String, usize, usize)>,
    receiver_layers: &mut Vec<LayerReceiverFaces>,
    final_normed: &mut Vec<(i64, i64)>,
    potential: &mut Vec<(i64, i64)>,
    terminal_refusal: &mut Option<String>,
) -> Result<(), String> {
    for (bound, census_at_launch, named, receipt_index) in deeds.drain(..) {
        let returned = bound.returned(census_at_launch).map_err(|obstruction| {
            format!(
                "segment receipt {receipt_index} did not return: {}",
                describe(&obstruction)
            )
        })?;
        if let Err(obstruction) = bound.standing(&returned) {
            obstructions.push((
                receipt_index,
                describe(&obstruction),
                returned.obstruction.refusals.len(),
                returned.obstruction.origins().count(),
            ));
        }
        let receipt = &mut receipts[receipt_index];
        receipt.lineage_empty = returned.stands();
        receipt.a_priori_held = returned.measured_octaves.iter().all(|(port, measured)| {
            bound.octave_field.get(port).copied().unwrap_or(0) >= *measured
        });
        for front in &returned.fronts {
            for reading in &front.readings {
                if reading.operation.starts_with("midpoint-quotient") {
                    receipt.quotients += 1;
                } else if reading.operation != "enter" && reading.operation != "carry" {
                    receipt.collapsed_width_sum += u128::from(reading.measured.width_sum);
                    receipt.collapsed_width_max =
                        receipt.collapsed_width_max.max(reading.measured.max_width);
                    receipt.collapsed_nonzero += u64::from(reading.measured.nonzero_widths);
                }
            }
        }
        if receiver_option == ReceiverOption::Complete {
            if let Some(layer) = receipt.layer {
                let ple = bound
                    .read_section(&returned, named[tower::PLE_SECTION])
                    .map_err(|obstruction| {
                        format!("layer {layer} PLE receiver: {}", describe(&obstruction))
                    })?;
                let contact = bound
                    .read_section(&returned, named[tower::CONTACT])
                    .map_err(|obstruction| {
                        format!("layer {layer} contact receiver: {}", describe(&obstruction))
                    })?;
                let layer_return = bound
                    .read_section(&returned, named[tower::LAYER_ENCLOSURE])
                    .map_err(|obstruction| {
                        format!("layer {layer} return receiver: {}", describe(&obstruction))
                    })?;
                receiver_layers.push(LayerReceiverFaces {
                    layer,
                    ple,
                    contact,
                    layer_return,
                });
            }
        }
        if receipt.layer.is_none() && !cultivation_present {
            match bound.read_section(&returned, named[tower::FINAL_NORMED]) {
                Ok(read) => *final_normed = read,
                Err(obstruction) => *terminal_refusal = Some(describe(&obstruction)),
            }
            match bound.read_terminal(&returned) {
                Ok(read) => *potential = read,
                Err(obstruction) => *terminal_refusal = Some(describe(&obstruction)),
            }
        }
    }
    Ok(())
}

/// What the whole circulation returned.
pub struct Circulated {
    pub tokens: Vec<usize>,
    pub segments: Vec<SegmentReceipt>,
    pub potential: Vec<(i64, i64)>,
    pub final_normed: Vec<(i64, i64)>,
    pub tower_work: ExactWork,
    pub streamed: StreamedCensus,
    pub census_before: TransferCensus,
    /// Surface census immediately after the terminal tower deed and before any W3 overlay.
    pub census_after_tower: TransferCensus,
    pub census_after: TransferCensus,
    pub census_at_loop_open: TransferCensus,
    pub census_at_loop_close: TransferCensus,
    pub peak_charged_octets: u64,
    pub wall_s: f64,
    pub loop_wall_s: f64,
    pub admission: MaterialAdmission,
    pub deed_launches: u64,
    /// Segments whose lineage carried a refusal, with the obstruction said whole, the population
    /// of the complete lineage and how many of them originated it.
    pub obstructions: Vec<(usize, String, usize, usize)>,
    /// The refusal a terminal read returned instead of words, where one did.
    pub terminal_refusal: Option<String>,
    /// **The §5.4 key this circulation's executables were bound under.** Founded, stated, and
    /// UNEXERCISED: no cache exists here and no reuse is claimed.
    pub graph_key: GraphKey,
    pub final_normed_bound: u32,
    pub potential_bound: u32,
    /// The receiver declaration used for this deed.  W2/W3 entry points use `Terminal`.
    pub receiver: ReceiverOption,
    /// Complete layer and terminal faces, populated only after the one terminal synchronization
    /// when `receiver == ReceiverOption::Complete`.  `None` is the historical narrow receiver.
    pub receiver_faces: Option<ReceiverFaces>,
    /// The actual per-segment/final admissions and their whole-tower identity.
    pub tower_admission: TowerAdmissionReceipt,
}

impl Circulated {
    /// Return the tower's resident and pooled transport testimony without converting absolute
    /// census windows into invented deltas.
    pub fn apparatus_census(&self) -> ApparatusCensus {
        ApparatusCensus {
            resident_before: self.census_before.clone(),
            resident_after_tower: self.census_after_tower.clone(),
            resident_after: self.census_after.clone(),
            overlay_before: None,
            overlay_after: None,
            streamed: self.streamed.clone(),
            tower_deed_launches: self.deed_launches,
            total_deed_launches: self.deed_launches,
            terminal_synchronizations: self.streamed.terminal_synchronizations,
        }
    }
}

impl CultivatedCirculated {
    /// Return the tower window plus the overlay's own absolute window. The overlay is not folded
    /// into the tower census, so its ingress/egress testimony cannot be counted twice.
    pub fn apparatus_census(&self) -> ApparatusCensus {
        ApparatusCensus {
            resident_before: self.execution.resident_transfer_before.clone(),
            resident_after_tower: self.base.census_after_tower.clone(),
            resident_after: self.execution.resident_transfer_after.clone(),
            overlay_before: Some(self.execution.overlay_transfer_before.clone()),
            overlay_after: Some(self.execution.overlay_transfer_after.clone()),
            streamed: self.execution.streamed.clone(),
            tower_deed_launches: self.base.deed_launches,
            total_deed_launches: self.total_deed_launches,
            terminal_synchronizations: self.execution.terminal_synchronizations,
        }
    }
}

/// One obstruction, said whole. The same shape `phoenix/conduct.rs` prints, restated here so the
/// streamed site depends on no other site.
pub fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => {
            format!("CoverBarrier at front {front}: {barriers:?}")
        }
        FrontPassageObstruction::Interchange { front, because, .. } => {
            format!("InterchangeRefusal at front {front}: {because:?}")
        }
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Refused {
            occurrence,
            operation,
            refusal,
            lineage,
            ..
        } => {
            format!(
                "the card refused at {occurrence:?} ({operation}): {refusal}; lineage {:?}",
                lineage.refusals
            )
        }
        FrontPassageObstruction::Sealed {
            occurrence,
            quotient,
            reopening,
        } => {
            format!(
                "the section at {occurrence:?} was sealed away by the fused quotient {quotient:?}; {reopening}"
            )
        }
    }
}

/// Read one BF16 word straight out of the container — the layer scalar, which is a host dyadic and
/// is mounted nowhere.
pub fn scalar_word_of(file: &std::fs::File, region: &StagedRegion) -> Result<u16, String> {
    let mut octets = [0u8; 2];
    file.read_exact_at(&mut octets, region.start)
        .map_err(|e| e.to_string())?;
    Ok(u16::from_le_bytes(octets))
}

fn tower_admission_receipt(
    deeds: Vec<crate::front_passage::DeedAdmission>,
) -> Result<TowerAdmissionReceipt, String> {
    let serialized = serde_json::to_string(&deeds)
        .map_err(|error| format!("serialize tower deed admissions: {error}"))?;
    let identity = format!("{:x}", Sha256::digest(serialized.as_bytes()));
    Ok(TowerAdmissionReceipt {
        deeds,
        serialized,
        identity,
    })
}

/// **The tower, as one streamed circulation.**
///
/// One pre-deed admission, 43 segments each bounded by a pinned-staging refill, 43 graph
/// executables launched onto one conducting current with no synchronization between them, and one
/// terminal synchronization. Between two segments the apparatus stages octets, crosses them,
/// mounts them and launches — and reads nothing.
#[allow(clippy::too_many_arguments)]
pub fn circulate<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    limit: usize,
    poison: bool,
) -> Result<Circulated, String> {
    match circulate_inner(
        surface,
        readout,
        source,
        tokens,
        grain,
        terms,
        chart,
        fuse,
        limit,
        poison,
        None,
        None,
        InterventionSite::Nowhere,
        &Intervention::None,
        ReceiverOption::Terminal,
    )? {
        CirculationOutput::Base(base) => Ok(base),
        CirculationOutput::Cultivated(_) => {
            Err("the no-overlay circulation returned a cultivated tail".to_owned())
        }
    }
}

/// Base W2 circulation with one typed intervention site and an optional complete receiver family.
/// The old [`circulate`] entry remains the exact no-intervention/narrow-receiver case.
#[allow(clippy::too_many_arguments)]
pub fn circulate_with_intervention<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    site: InterventionSite,
    intervention: &Intervention,
    receiver: ReceiverOption,
) -> Result<Circulated, String> {
    match circulate_inner(
        surface,
        readout,
        source,
        tokens,
        grain,
        terms,
        chart,
        fuse,
        tower::LAYERS,
        false,
        None,
        None,
        site,
        intervention,
        receiver,
    )? {
        CirculationOutput::Base(base) => Ok(base),
        CirculationOutput::Cultivated(_) => {
            Err("the intervention-aware base circulation returned a cultivated tail".to_owned())
        }
    }
}

/// W3's separate typed entry. It conducts the complete W2 tower and adds exactly one overlay deed
/// to the same conducting stream before the sole terminal synchronization.
#[allow(clippy::too_many_arguments)]
pub fn circulate_cultivated<'chart, 'request>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    request: &'request CultivationRequest<'request>,
) -> Result<CultivatedCirculated, String> {
    match circulate_inner(
        surface,
        readout,
        source,
        tokens,
        grain,
        terms,
        chart,
        fuse,
        tower::LAYERS,
        false,
        None,
        Some(request),
        InterventionSite::Nowhere,
        &Intervention::None,
        ReceiverOption::Terminal,
    )? {
        CirculationOutput::Cultivated(cultivated) => Ok(cultivated),
        CirculationOutput::Base(_) => {
            Err("the cultivated circulation returned no overlay tail".to_owned())
        }
    }
}

/// Cultivated W3 circulation with the same typed intervention site as the base tower.  The
/// overlay is launched after the intervened tower on that tower's conducting stream, before its
/// sole terminal synchronization.
#[allow(clippy::too_many_arguments)]
pub fn circulate_cultivated_with_intervention<'chart, 'request>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    site: InterventionSite,
    intervention: &Intervention,
    receiver: ReceiverOption,
    request: &'request CultivationRequest<'request>,
) -> Result<CultivatedCirculated, String> {
    match circulate_inner(
        surface,
        readout,
        source,
        tokens,
        grain,
        terms,
        chart,
        fuse,
        tower::LAYERS,
        false,
        None,
        Some(request),
        site,
        intervention,
        receiver,
    )? {
        CirculationOutput::Cultivated(cultivated) => Ok(cultivated),
        CirculationOutput::Base(_) => {
            Err("the intervention-aware cultivated circulation returned no overlay tail".to_owned())
        }
    }
}

/// The same cultivated circulation with an addressed partition of the entering source rows. The
/// partition is a receiver presentation: all token rows still cross, and each block's exact mean
/// becomes one row of the inherited tower.
#[allow(clippy::too_many_arguments)]
pub fn circulate_cultivated_with_partitioned_intervention<'chart, 'request>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    partition_boundaries: &[u32],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    site: InterventionSite,
    intervention: &Intervention,
    receiver: ReceiverOption,
    request: &'request CultivationRequest<'request>,
) -> Result<CultivatedCirculated, String> {
    match circulate_inner(
        surface,
        readout,
        source,
        tokens,
        grain,
        terms,
        chart,
        fuse,
        tower::LAYERS,
        false,
        Some(partition_boundaries),
        Some(request),
        site,
        intervention,
        receiver,
    )? {
        CirculationOutput::Cultivated(cultivated) => Ok(cultivated),
        CirculationOutput::Base(_) => {
            Err("the partitioned cultivated circulation returned no overlay tail".to_owned())
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn circulate_inner<'chart, 'request>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    // `limit`: how many source layers to conduct. The whole tower is `tower::LAYERS`; a control
    // conducts fewer and the final boundary still runs on whatever standing arrived.
    // `poison`: a control — one entering codeword replaced by a pattern that is not a finite BF16
    // value, so the mouth refuses it on the card and every successor in that deed carries it.
    limit: usize,
    poison: bool,
    partition_boundaries: Option<&[u32]>,
    cultivation: Option<&'request CultivationRequest<'request>>,
    intervention_site: InterventionSite,
    intervention: &Intervention,
    receiver_option: ReceiverOption,
) -> Result<CirculationOutput, String> {
    let clock = Instant::now();
    let census_before = surface.census();
    let passage = FrontPassage::new(surface, grain);
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let no_intervention = Intervention::None;
    if tokens.is_empty() {
        return Err("the tower received no entering rows".to_owned());
    }
    let model_rows = match partition_boundaries {
        Some(boundaries)
            if boundaries.len() >= 2
                && boundaries[0] == 0
                && boundaries.last().copied() == Some(tokens.len() as u32)
                && boundaries.windows(2).all(|pair| pair[0] < pair[1]) =>
        {
            boundaries.len() - 1
        }
        Some(boundaries) => {
            return Err(format!(
                "the entering partition does not cover {} source rows exactly: {boundaries:?}",
                tokens.len()
            ));
        }
        None => tokens.len(),
    };

    // ---------------------------------------------------------------------------------------
    // before the deed: the segments, the admission, the standing, and the one native-rest occurrence
    // ---------------------------------------------------------------------------------------
    let mut layer_segments = Vec::with_capacity(tower::LAYERS);
    for layer in 0..tower::LAYERS {
        layer_segments.push(layer_segment(source, layer, 0, layer % 3)?);
    }
    let last = final_segment(source, 0, FINAL_PINNED)?;
    let staging_shapes = slot_shapes(&layer_segments, &last);
    let shapes = resident_window_slot_shape(&layer_segments, &last);
    let refills = vec![tower::LAYERS as u64 + 1];
    // Every resident auxiliary below is a separate allocation. Keep the plan decomposed so the
    // card's allocation-grain rounding is applied to each mounted band/position population.
    let mut auxiliaries = vec![
        PooledMaterialAuxiliary::BandElements(tower::SLIDING_HEAD / 2),
        PooledMaterialAuxiliary::BandElements(tower::FULL_HEAD / 2),
        PooledMaterialAuxiliary::Positions(model_rows),
    ];
    if let Some(boundaries) = partition_boundaries {
        auxiliaries.push(PooledMaterialAuxiliary::Positions(boundaries.len()));
    }
    let layer_site = |site: InterventionSite| match site {
        InterventionSite::EveryLayer => true,
        InterventionSite::Layer(_) => true,
        InterventionSite::Nowhere | InterventionSite::Final => false,
    };
    if layer_site(intervention_site) {
        if matches!(intervention, Intervention::IdentityChronology) {
            match intervention_site {
                InterventionSite::EveryLayer => {
                    auxiliaries.push(PooledMaterialAuxiliary::BandElements(
                        tower::SLIDING_HEAD / 2,
                    ));
                    auxiliaries.push(PooledMaterialAuxiliary::BandElements(tower::FULL_HEAD / 2));
                }
                InterventionSite::Layer(layer) => match Species::of(layer) {
                    Species::Sliding => auxiliaries.push(PooledMaterialAuxiliary::BandElements(
                        tower::SLIDING_HEAD / 2,
                    )),
                    Species::Full => auxiliaries
                        .push(PooledMaterialAuxiliary::BandElements(tower::FULL_HEAD / 2)),
                },
                InterventionSite::Nowhere | InterventionSite::Final => {}
            }
        }
        if matches!(intervention, Intervention::ReversedPositions) {
            auxiliaries.push(PooledMaterialAuxiliary::Positions(model_rows));
        }
        if matches!(
            intervention,
            Intervention::PermuteReceiverHeads { .. } | Intervention::PermuteCarriedHeads { .. }
        ) {
            auxiliaries.push(PooledMaterialAuxiliary::Positions(tower::HEADS));
        }
    }
    let prediction = passage.predict_pooled_material(&shapes, &refills, &auxiliaries);
    let admission = passage
        .admit_material(&prediction)
        .map_err(|o| format!("the tower's pooled material refused: {}", describe(&o)))?;

    let identity_before = source.source_identity();

    // THREE pinned slots for the source layers and one for the final boundary. Three, not two,
    // because the staged read runs two segments ahead of the mount while the crossing runs one
    // ahead: with two slots the read of segment k+2 would have to wait on the copy of segment k+1,
    // which is the copy that is supposed to be crossing while segment k's graph conducts.
    let pinned = vec![
        staging_shapes[0].stored_octets,
        staging_shapes[0].stored_octets,
        staging_shapes[0].stored_octets,
        staging_shapes[2].stored_octets,
    ];
    let mut circulation =
        StreamedCirculation::open(surface, std::slice::from_ref(&staging_shapes[0]), &pinned)
            .map_err(|e| e.to_string())?;

    // The material, held for the WHOLE circulation. The bands, the positions and the entering
    // codewords cross once; only the maps and the carried standings move between segments.
    let mut material = ResidentMaterial::empty();
    let band_terms = cultivation
        .map(|request| request.band_terms)
        .unwrap_or(tower::BAND_TERMS);
    if band_terms == 0 {
        return Err("runtime band chronology aperture is zero".to_owned());
    }
    let sliding_bands = tower::found_bands(Species::Sliding, band_terms)?;
    let full_bands = tower::found_bands(Species::Full, band_terms)?;
    material.bands.insert(
        tower::SLIDING_BANDS.to_owned(),
        (
            surface
                .mount_bands(&sliding_bands, tower::BAND_GRAIN)
                .map_err(|e| e.to_string())?,
            (model_rows - 1) as u32,
        ),
    );
    material.bands.insert(
        tower::FULL_BANDS.to_owned(),
        (
            surface
                .mount_bands(&full_bands, tower::BAND_GRAIN)
                .map_err(|e| e.to_string())?,
            (model_rows - 1) as u32,
        ),
    );
    let positions: Vec<u32> = (0..model_rows as u32).collect();
    let reversed_positions: Vec<u32> = positions.iter().copied().rev().collect();
    material.positions = Some(
        surface
            .mount_positions(&positions)
            .map_err(|e| e.to_string())?,
    );
    if let Some(boundaries) = partition_boundaries {
        material.arrays.insert(
            tower::INPUT_PARTITION.to_owned(),
            surface
                .mount_positions(boundaries)
                .map_err(|error| error.to_string())?,
        );
    }
    // Keep both position charts resident for the whole circulation. Swapping ownership between
    // the active/inactive slots cannot free a buffer still named by an earlier launched graph.
    let mut alternate_positions = if intervention_site != InterventionSite::Nowhere
        && matches!(intervention, Intervention::ReversedPositions)
    {
        Some(
            surface
                .mount_positions(&reversed_positions)
                .map_err(|e| e.to_string())?,
        )
    } else {
        None
    };
    // A permutation is one immutable auxiliary population for the whole selected site. Keeping
    // it in `material.arrays` avoids dropping a buffer still named by an earlier graph when the
    // site is EveryLayer.

    // The runtime-supplied entering rows, read ONCE for the whole tower: the embedding row of each
    // token, and its per-layer embedding row, which every layer slices differently.
    let mut entering = Vec::with_capacity(tokens.len() * tower::HIDDEN);
    let mut per_layer_rows: Vec<Vec<u16>> = Vec::with_capacity(tokens.len());
    for token in tokens {
        let (row, width) = source.rows(tower::EMBED, *token, 1)?;
        if width != tower::HIDDEN {
            return Err(format!("{} is {width} wide", tower::EMBED));
        }
        entering.extend(row);
        let (row, _) = source.rows(tower::PLE_EMBED, *token, 1)?;
        per_layer_rows.push(row);
    }
    if poison {
        // 0x7F80 is a BF16 infinity: not a finite value, so the mouth raises MALFORMED on the card
        // rather than placing anything, and the refusal travels the deed's declared lineage.
        entering[0] = 0x7F80;
    }
    material.entering.insert(
        tower::ENTERING.to_owned(),
        EnteringRows {
            words: entering,
            rows: tokens.len(),
            width: tower::HIDDEN,
        },
    );

    // Every layer's scalar, read before the deed: one stored word each, a host dyadic, mounted
    // nowhere. Reading them here keeps the loop's exterior contact to the staged refill alone.
    let mut layer_scalars = Vec::with_capacity(tower::LAYERS);
    for segment in &layer_segments {
        let region = segment
            .scalar
            .as_ref()
            .ok_or("the layer segment carries no layer scalar")?;
        let file = source.file()?;
        layer_scalars.push(
            Dyadic::of_bfloat16_bits(scalar_word_of(file, region)?).map_err(|e| e.to_string())?,
        );
    }

    // The W3 candidate, exact factor residency, and pure overlay work are admitted before the
    // first W2 launch; the final bind must agree with this receipt after h and y0 are released.
    let (mut overlay_material, pre_admission) = if let Some(request) = cultivation {
        let receiver_rows = match receiver_option {
            ReceiverOption::Terminal => 1,
            ReceiverOption::Complete => model_rows,
        };
        let (material, receipt) = streamed_cultivation::prepare(
            surface,
            readout,
            &passage,
            request,
            receiver_rows,
            grain,
        )?;
        (Some(material), Some(receipt))
    } else {
        (None, None)
    };

    // ---------------------------------------------------------------------------------------
    // the circulation
    // ---------------------------------------------------------------------------------------
    let census_at_loop_open = surface.census();
    let loop_clock = Instant::now();
    let mut carried: Option<(Rc<ResidentSection<'chart>>, u32)> = None;
    let mut shared: BTreeMap<&'chart str, (Rc<ResidentSection<'chart>>, u32)> = BTreeMap::new();
    let mut bound_deeds: Vec<BoundDeed<'chart>> = Vec::new();
    let mut receipts: Vec<SegmentReceipt> = Vec::new();
    let mut potential = Vec::new();
    let mut final_normed = Vec::new();
    let mut obstructions: Vec<(usize, String, usize, usize)> = Vec::new();
    let mut terminal_refusal: Option<String> = None;
    let mut receiver_layers = Vec::new();
    let mut reductions: Vec<(String, u64)> = Vec::new();
    let mut tower_work = ExactWork::nothing();
    let mut peak_charged_octets = 0u64;
    let mut deed_launches = 0u64;
    let mut overlay_bound: Option<cultivation_overlay::OverlayPassage<'chart>> = None;
    let mut overlay_census: Option<TransferCensus> = None;
    let mut overlay_work: Option<ExactWork> = None;
    let mut overlay_apparatus: Option<crate::front_passage::ApparatusPrediction> = None;
    let mut overlay_admission: Option<crate::front_passage::DeedAdmission> = None;
    let mut overlay_execution: Option<OverlayExecutionIdentity> = None;
    let mut overlay_return: Option<crate::front_passage::PassageReturn> = None;
    let mut positions_reversed = false;
    let mut tower_deeds = Vec::with_capacity(tower::LAYERS + 1);

    // **The pipeline.** The staged read runs two segments ahead of the mount and the crossing one
    // ahead, so segment k+1's copy is issued IMMEDIATELY after segment k's graph is launched and
    // crosses while that graph conducts. Measured 2026-08-19: with the copy issued after the next
    // staged read instead, every copy landed after the graph it was meant to overlap and the
    // profiler read 0 ns of overlap — every stream asynchronous, and nothing concurrent.
    let layer_count = tower::LAYERS.min(limit);
    let at = |i: usize| -> &Segment { &layer_segments[i] };
    let mut offsets: Vec<Vec<usize>> = vec![Vec::new(); layer_count];
    let mut requests: Vec<Vec<crate::embedding_fiber::PooledMount>> = vec![Vec::new(); layer_count];
    let mut stage_wall: Vec<f64> = vec![0.0; layer_count];
    {
        let first = at(0);
        let clock = Instant::now();
        let file = source.file()?;
        offsets[0] = circulation
            .stage(first.pinned, file, source.file_octets()?, &first.regions)
            .map_err(|e| e.to_string())?;
        stage_wall[0] = clock.elapsed().as_secs_f64();
        requests[0] = circulation
            .cross(first.slot, first.pinned, &offsets[0], &first.regions)
            .map_err(|e| e.to_string())?;
        if layer_count > 1 {
            let second = at(1);
            let clock = Instant::now();
            let file = source.file()?;
            offsets[1] = circulation
                .stage(second.pinned, file, source.file_octets()?, &second.regions)
                .map_err(|e| e.to_string())?;
            stage_wall[1] = clock.elapsed().as_secs_f64();
        }
    }

    for layer in 0..tower::LAYERS.min(limit) {
        let segment = &layer_segments[layer];
        let species = Species::of(layer);
        let role = KvRole::of(layer);
        let layer_scalar = layer_scalars[layer];
        let stage_wall_s = stage_wall[layer];
        // the layer's slice of each token's per-layer embedding row
        let mut per_layer = Vec::with_capacity(tokens.len() * tower::PLE_WIDTH);
        for row in &per_layer_rows {
            let from = layer * tower::PLE_WIDTH;
            if row.len() < from + tower::PLE_WIDTH {
                return Err(format!("{} is {} wide", tower::PLE_EMBED, row.len()));
            }
            per_layer.extend_from_slice(&row[from..from + tower::PLE_WIDTH]);
        }
        material.entering.insert(
            super::site::PLE_ENTERING.to_owned(),
            EnteringRows {
                words: per_layer,
                rows: tokens.len(),
                width: tower::PLE_WIDTH,
            },
        );

        // These are the only extra apparatus faces needed by tower interventions.  They are
        // mounted for the selected layer before its graph is bound; no semantic section is read
        // and no host branch occurs between launches.
        let applied = if intervention_site.applies_to_layer(layer) {
            intervention
        } else {
            &no_intervention
        };
        if positions_reversed && !matches!(applied, Intervention::ReversedPositions) {
            std::mem::swap(&mut material.positions, &mut alternate_positions);
            positions_reversed = false;
        }
        if matches!(applied, Intervention::IdentityChronology) {
            let pairs = species.head_width() / 2;
            let identity = tower::identity_bands(pairs);
            let identity_name = match species {
                Species::Sliding => tower::IDENTITY_BANDS,
                Species::Full => tower::IDENTITY_BANDS_FULL,
            };
            if !material.bands.contains_key(identity_name) {
                material.bands.insert(
                    identity_name.to_owned(),
                    (
                        surface
                            .mount_bands(&identity, tower::BAND_GRAIN)
                            .map_err(|e| e.to_string())?,
                        (model_rows - 1) as u32,
                    ),
                );
            }
        }
        if matches!(applied, Intervention::ReversedPositions) {
            if !positions_reversed {
                std::mem::swap(&mut material.positions, &mut alternate_positions);
                positions_reversed = true;
            }
        }
        if let Intervention::PermuteReceiverHeads { a, b }
        | Intervention::PermuteCarriedHeads { a, b } = applied
        {
            if material.arrays.contains_key(tower::HEAD_PERMUTATION) {
                // The same immutable permutation is valid at every selected layer.
            } else {
                let permutation: Vec<u32> = tower::swap_permutation(tower::HEADS, *a, *b)
                    .into_iter()
                    .map(|index| index as u32)
                    .collect();
                material.arrays.insert(
                    tower::HEAD_PERMUTATION.to_owned(),
                    surface
                        .mount_positions(&permutation)
                        .map_err(|e| e.to_string())?,
                );
            }
        }

        // --- the mouth, on its own current, over the slot the copy already filled ---
        let mount_clock = Instant::now();
        let mounted = circulation
            .mount(segment.slot, segment.pinned, &requests[layer])
            .map_err(|e| e.to_string())?;
        material.populations.clear();
        for (name, pooled) in segment.names.iter().zip(mounted) {
            material.populations.insert(
                name.clone(),
                MountedPopulation {
                    readout: pooled.readout,
                    mass_value_octaves: pooled.mass_value_octaves,
                },
            );
        }
        let mount_wall_s = mount_clock.elapsed().as_secs_f64();

        // --- the standings this layer enters on ---
        material.standings.clear();
        if let Some((section, bound)) = &carried {
            material.standings.insert(
                tower::CARRIED_STANDING.to_owned(),
                (Rc::clone(section), *bound),
            );
        }
        if role == KvRole::Shared {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = shared
                .get(k_name)
                .ok_or_else(|| format!("layer {layer}: no shared K standing"))?;
            let (v, vb) = shared
                .get(v_name)
                .ok_or_else(|| format!("layer {layer}: no shared V standing"))?;
            material
                .standings
                .insert(k_name.to_owned(), (Rc::clone(k), *kb));
            material
                .standings
                .insert(v_name.to_owned(), (Rc::clone(v), *vb));
        }

        // --- the diagram, and the apparatus fusion the receiver's declarations admit ---
        let bind_clock = Instant::now();
        let entry = if layer == 0 {
            Entry::Rows
        } else {
            Entry::Carried
        };
        let mut founded = tower::found_layer(
            layer,
            entry,
            chart,
            &scales,
            terms,
            layer_scalar,
            applied,
            model_rows,
            match partition_boundaries {
                Some(boundaries) => tower::InputSectionReceiver::PartitionMeans(boundaries),
                None => tower::InputSectionReceiver::SourceRows,
            },
        )?;
        let terminal = founded.returns[tower::LAYER_RETURN];
        let mut declared = BTreeSet::new();
        if receiver_option == ReceiverOption::Complete {
            declared.insert(founded.returns[tower::PLE_SECTION]);
            declared.insert(founded.returns[tower::CONTACT]);
            // The enclosure is the receiver-visible layer-return face.  The later
            // `LAYER_RETURN` is the standing transferred to the next deed and is released as
            // ownership crosses the layer boundary.
            declared.insert(founded.returns[tower::LAYER_ENCLOSURE]);
            declared.insert(founded.returns[tower::LAYER_RETURN]);
        }
        let (fusable, refused) = if fuse {
            factored_seals(&founded.complex, &founded.realization, terminal, &declared)
        } else {
            (Vec::new(), Vec::new())
        };
        for occurrence in &fusable {
            founded
                .realization
                .bind(*occurrence, SealedMidpointQuotient);
        }
        let bound = match passage.bind(
            &founded.complex,
            &founded.realization,
            &material,
            source.occurrence(),
            &receiver,
            Some(&admission),
            terminal,
        ) {
            Ok(bound) => bound,
            Err(obstruction) if residency_pressure(&obstruction) && !bound_deeds.is_empty() => {
                circulation
                    .residency_boundary()
                    .map_err(|error| error.to_string())?;
                discharge_window(
                    &mut bound_deeds,
                    &mut receipts,
                    receiver_option,
                    cultivation.is_some(),
                    &mut obstructions,
                    &mut receiver_layers,
                    &mut final_normed,
                    &mut potential,
                    &mut terminal_refusal,
                )?;
                passage
                    .bind(
                        &founded.complex,
                        &founded.realization,
                        &material,
                        source.occurrence(),
                        &receiver,
                        Some(&admission),
                        terminal,
                    )
                    .map_err(|retry| {
                        format!(
                            "layer {layer} refused after a pressure-derived resident boundary: {}",
                            describe(&retry)
                        )
                    })?
            }
            Err(obstruction) => {
                return Err(format!(
                    "layer {layer} refused at bind: {}",
                    describe(&obstruction)
                ));
            }
        };
        let bind_wall_s = bind_clock.elapsed().as_secs_f64();
        if reductions.is_empty() {
            for front in bound.fronts() {
                for coupling in &front.couplings {
                    reductions.push((coupling.plan.kernel.to_owned(), coupling.plan.extent));
                }
            }
        }
        peak_charged_octets = peak_charged_octets
            .max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
        let (graph, _) = bound.graph();
        let graph_nodes = graph.nodes;
        let graph_edges = graph.edges;

        // --- the deed: launched onto the conducting current, and NOT waited for ---
        circulation
            .admit_segment(segment.slot)
            .map_err(|e| e.to_string())?;
        tower_deeds.push(bound.admission.clone());
        let census_at_launch = bound
            .launch_on(&surface.mode(), circulation.conducting())
            .map_err(|o| format!("layer {layer} refused at launch: {}", describe(&o)))?;
        circulation
            .conducted(segment.slot)
            .map_err(|e| e.to_string())?;
        deed_launches += 1;
        tower_work = tower_work.then(&bound.deed_prediction);

        // The next segment's copy, issued now so it crosses while THIS deed conducts, and the one
        // after it staged from the container. Neither reads a semantic value; both are transports.
        if layer + 1 < layer_count {
            let next = at(layer + 1);
            requests[layer + 1] = circulation
                .cross(next.slot, next.pinned, &offsets[layer + 1], &next.regions)
                .map_err(|e| e.to_string())?;
        }
        if layer + 2 < layer_count {
            let after = at(layer + 2);
            let clock = Instant::now();
            let file = source.file()?;
            offsets[layer + 2] = circulation
                .stage(after.pinned, file, source.file_octets()?, &after.regions)
                .map_err(|e| e.to_string())?;
            stage_wall[layer + 2] = clock.elapsed().as_secs_f64();
        }

        let mut bound = bound;
        // The standings the next deeds carry. Releasing moves ownership of a device section; it
        // reads nothing and crosses nothing.
        if role == KvRole::OwnAndStore {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = bound
                .release_section(founded.returns[tower::K_STANDING])
                .ok_or("K standing")?;
            let (v, vb) = bound
                .release_section(founded.returns[tower::V_STANDING])
                .ok_or("V standing")?;
            shared.insert(k_name, (Rc::new(k), kb));
            shared.insert(v_name, (Rc::new(v), vb));
        }
        let (out, ob) = bound.release_section(terminal).ok_or("layer return")?;
        carried = Some((Rc::new(out), ob));

        receipts.push(SegmentReceipt {
            layer: Some(layer),
            slot: segment.slot,
            maps: segment.regions.len(),
            species: Some(species),
            role: Some(role),
            operations: founded.complex.operations.len(),
            fronts: bound.fronts().len(),
            graph_nodes,
            graph_edges,
            captured_launches: bound.apparatus_prediction.captured_launches,
            seals_fused: fusable.len(),
            seals_refused: refused,
            quotients: 0,
            collapsed_width_sum: 0,
            collapsed_width_max: 0,
            collapsed_nonzero: 0,
            lineage_empty: false,
            a_priori_held: false,
            every_front_certified: bound
                .fronts()
                .iter()
                .all(|f| f.certificate.because().is_none()),
            deed: bound.deed_prediction.clone(),
            material_resident_octets: material.resident_octets(),
            stage_wall_s,
            mount_wall_s,
            bind_wall_s,
        });
        let mut named: BTreeMap<&'chart str, EventId> = BTreeMap::new();
        for (name, event) in &founded.returns {
            named.insert(name, *event);
        }
        bound_deeds.push((bound, census_at_launch, named, receipts.len() - 1));
    }

    // --- the final deed: retire the mutually-exclusive layer-map slot, then found the larger
    // final-table slot. The carried semantic standing survives this exterior apparatus rebase. ---
    circulation
        .retire_slots()
        .map_err(|error| error.to_string())?;
    discharge_window(
        &mut bound_deeds,
        &mut receipts,
        receiver_option,
        cultivation.is_some(),
        &mut obstructions,
        &mut receiver_layers,
        &mut final_normed,
        &mut potential,
        &mut terminal_refusal,
    )?;
    material.standings.clear();
    shared.clear();
    circulation
        .found_slots(std::slice::from_ref(&staging_shapes[2]))
        .map_err(|error| error.to_string())?;
    let stage_clock = Instant::now();
    let final_offsets = circulation
        .stage(
            last.pinned,
            source.file()?,
            source.file_octets()?,
            &last.regions,
        )
        .map_err(|error| error.to_string())?;
    let stage_wall_s = stage_clock.elapsed().as_secs_f64();
    let final_requests = circulation
        .cross(last.slot, last.pinned, &final_offsets, &last.regions)
        .map_err(|error| error.to_string())?;
    let mount_clock = Instant::now();
    let mounted = circulation
        .mount(last.slot, last.pinned, &final_requests)
        .map_err(|e| e.to_string())?;
    material.populations.clear();
    for (name, pooled) in last.names.iter().zip(mounted) {
        material.populations.insert(
            name.clone(),
            MountedPopulation {
                readout: pooled.readout,
                mass_value_octaves: pooled.mass_value_octaves,
            },
        );
    }
    let mount_wall_s = mount_clock.elapsed().as_secs_f64();
    material.standings.clear();
    let (section, bound_octaves) = carried.take().ok_or("no carried standing")?;
    material
        .standings
        .insert(tower::CARRIED_STANDING.to_owned(), (section, bound_octaves));
    let bind_clock = Instant::now();
    let applied_final = if intervention_site.applies_to_final() {
        intervention
    } else {
        &no_intervention
    };
    let output_receiver = match receiver_option {
        ReceiverOption::Terminal => tower::OutputSectionReceiver::TerminalRow,
        ReceiverOption::Complete => tower::OutputSectionReceiver::Whole,
    };
    let mut founded = tower::found_final(chart, applied_final, &scales, output_receiver)?;
    let terminal = founded.returns[tower::POTENTIAL];
    // The final normed standing is a face this receiver reads, and it is itself the QUOTIENT: its
    // own face is the collapsed one, which the fused seal writes into its predecessor's buffer and
    // `read_section` resolves through. Nothing is declared, because the fusion condition is about a
    // quotient's PREDECESSOR and no receiver reads the pre-quotient enclosure here.
    let mut declared: BTreeSet<EventId> = BTreeSet::new();
    if receiver_option == ReceiverOption::Complete {
        declared.insert(founded.returns[tower::FINAL_NORMED]);
        declared.insert(founded.returns[tower::POTENTIAL]);
    }
    let passage_final = FrontPassage::new(surface, grain);
    let (fusable, refused) = if fuse {
        factored_seals(&founded.complex, &founded.realization, terminal, &declared)
    } else {
        (Vec::new(), Vec::new())
    };
    for occurrence in &fusable {
        founded
            .realization
            .bind(*occurrence, SealedMidpointQuotient);
    }
    let bound = match passage_final.bind(
        &founded.complex,
        &founded.realization,
        &material,
        source.occurrence(),
        &receiver,
        Some(&admission),
        terminal,
    ) {
        Ok(bound) => bound,
        Err(obstruction) if residency_pressure(&obstruction) && !bound_deeds.is_empty() => {
            circulation
                .residency_boundary()
                .map_err(|error| error.to_string())?;
            discharge_window(
                &mut bound_deeds,
                &mut receipts,
                receiver_option,
                cultivation.is_some(),
                &mut obstructions,
                &mut receiver_layers,
                &mut final_normed,
                &mut potential,
                &mut terminal_refusal,
            )?;
            passage_final
                .bind(
                    &founded.complex,
                    &founded.realization,
                    &material,
                    source.occurrence(),
                    &receiver,
                    Some(&admission),
                    terminal,
                )
                .map_err(|retry| {
                    format!(
                        "the final deed refused after a pressure-derived resident boundary: {}",
                        describe(&retry)
                    )
                })?
        }
        Err(obstruction) => {
            return Err(format!(
                "the final deed refused at bind: {}",
                describe(&obstruction)
            ));
        }
    };
    let final_normed_bound = *bound
        .octave_field
        .get(&OccurrencePort::output(
            founded.returns[tower::FINAL_NORMED],
            0,
        ))
        .ok_or("W2 final normed bound is absent")?;
    let potential_bound = *bound
        .octave_field
        .get(&OccurrencePort::output(
            founded.returns[tower::POTENTIAL],
            0,
        ))
        .ok_or("W2 potential bound is absent")?;
    let bind_wall_s = bind_clock.elapsed().as_secs_f64();
    peak_charged_octets = peak_charged_octets
        .max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
    let (graph, _) = bound.graph();
    let (graph_nodes, graph_edges) = (graph.nodes, graph.edges);
    circulation
        .admit_segment(last.slot)
        .map_err(|e| e.to_string())?;
    tower_deeds.push(bound.admission.clone());
    let census_at_launch = bound
        .launch_on(&surface.mode(), circulation.conducting())
        .map_err(|o| format!("the final deed refused at launch: {}", describe(&o)))?;
    circulation
        .conducted(last.slot)
        .map_err(|e| e.to_string())?;
    deed_launches += 1;
    tower_work = tower_work.then(&bound.deed_prediction);
    receipts.push(SegmentReceipt {
        layer: None,
        slot: last.slot,
        maps: last.regions.len(),
        species: None,
        role: None,
        operations: founded.complex.operations.len(),
        fronts: bound.fronts().len(),
        graph_nodes,
        graph_edges,
        captured_launches: bound.apparatus_prediction.captured_launches,
        seals_fused: fusable.len(),
        seals_refused: refused,
        quotients: 0,
        collapsed_width_sum: 0,
        collapsed_width_max: 0,
        collapsed_nonzero: 0,
        lineage_empty: false,
        a_priori_held: false,
        every_front_certified: bound
            .fronts()
            .iter()
            .all(|f| f.certificate.because().is_none()),
        deed: bound.deed_prediction.clone(),
        material_resident_octets: material.resident_octets(),
        stage_wall_s,
        mount_wall_s,
        bind_wall_s,
    });
    let mut named: BTreeMap<&'chart str, EventId> = BTreeMap::new();
    for (name, event) in &founded.returns {
        named.insert(name, *event);
    }
    bound_deeds.push((bound, census_at_launch, named, receipts.len() - 1));
    // This is the tower-only resident window. W3's overlay starts after this point and owns a
    // separate census window, so the two are never presented as one additive delta.
    let census_after_tower = surface.census();

    // --- W3 tail: release h and y0 from the final W2 deed, then launch once on the same stream ---
    if let Some(request) = cultivation {
        let (final_bound, _, final_named, _) =
            bound_deeds.last_mut().ok_or("W2 final deed is absent")?;
        let h_event = *final_named
            .get(tower::FINAL_NORMED)
            .ok_or("W2 final normed return is absent")?;
        let y0_event = *final_named
            .get(tower::POTENTIAL)
            .ok_or("W2 potential return is absent")?;
        let (h, h_bound) = final_bound
            .release_section(h_event)
            .ok_or("W2 final normed standing could not be released")?;
        let (y0, y0_bound) = final_bound
            .release_section(y0_event)
            .ok_or("W2 base potential could not be released")?;
        if h_bound != request.input_bound || y0_bound != request.predecessor_bound {
            return Err(format!(
                "W3 bound drift: requested h/y0 {}/{} but W2 released {}/{}",
                request.input_bound, request.predecessor_bound, h_bound, y0_bound
            ));
        }
        let overlay_material_ref = overlay_material
            .as_mut()
            .ok_or("W3 factor material is absent")?;
        cultivation_overlay::carry_standing(overlay_material_ref, "phoenix.overlay.h", h, h_bound);
        cultivation_overlay::carry_standing(
            overlay_material_ref,
            "phoenix.overlay.y0",
            y0,
            y0_bound,
        );
        cultivation_overlay::inspect_extents(request.candidate, overlay_material_ref)?;
        let pre = pre_admission
            .as_ref()
            .ok_or("W3 pre-admission receipt is absent")?;
        let overlay = request
            .candidate
            .bind(
                surface,
                overlay_material_ref,
                request.witness,
                &receiver,
                Some(&pre.material_admission),
                "phoenix.overlay.h",
                "phoenix.overlay.y0",
                request.input_bound,
                grain,
                Some(request.derivation),
            )
            .map_err(|error| format!("W3 overlay refused at bind: {}", describe(&error)))?;
        if overlay.passage.deed_prediction != pre.overlay_work {
            return Err(format!(
                "W3 overlay work disagrees with its pre-admission prediction: predicted={:?}, compiled={:?}",
                pre.overlay_work, overlay.passage.deed_prediction,
            ));
        }
        if u64::from(overlay.passage.apparatus_prediction.captured_launches) != pre.overlay_launches
        {
            return Err(
                "W3 overlay launch count disagrees with its pre-admission prediction".to_owned(),
            );
        }
        overlay_work = Some(overlay.passage.deed_prediction.clone());
        overlay_apparatus = Some(overlay.passage.apparatus_prediction.clone());
        overlay_admission = Some(overlay.passage.admission.clone());
        overlay_execution = Some(streamed_cultivation::execution_identity(&overlay));
        overlay_census = Some(
            overlay
                .passage
                .launch_on(&surface.mode(), circulation.conducting())
                .map_err(|error| format!("W3 overlay refused at launch: {}", describe(&error)))?,
        );
        overlay_bound = Some(overlay);
    }

    let census_at_loop_close = surface.census();
    let loop_wall_s = loop_clock.elapsed().as_secs_f64();

    // ---------------------------------------------------------------------------------------
    // ONE terminal synchronization, and only then a reading
    // ---------------------------------------------------------------------------------------
    circulation.terminal().map_err(|e| e.to_string())?;
    let streamed = circulation.census().clone();

    discharge_window(
        &mut bound_deeds,
        &mut receipts,
        receiver_option,
        cultivation.is_some(),
        &mut obstructions,
        &mut receiver_layers,
        &mut final_normed,
        &mut potential,
        &mut terminal_refusal,
    )?;

    let mut cultivated_potential = Vec::new();
    let mut base_potential_digest = String::new();
    if cultivation.is_some() {
        let candidate_material = overlay_material
            .as_ref()
            .ok_or("W3 factor material disappeared")?;
        let h = &candidate_material
            .standings
            .get("phoenix.overlay.h")
            .ok_or("W3 h standing disappeared")?
            .0;
        let y0 = &candidate_material
            .standings
            .get("phoenix.overlay.y0")
            .ok_or("W3 y0 standing disappeared")?
            .0;
        final_normed = surface
            .read_out(h)
            .map_err(|error| format!("W3 h return: {error}"))?;
        potential = surface
            .read_out(y0)
            .map_err(|error| format!("W3 base potential return: {error}"))?;
        base_potential_digest = digest_face(&potential, grain);
        let overlay = overlay_bound
            .as_ref()
            .ok_or("W3 overlay passage disappeared")?;
        let returned = overlay
            .passage
            .returned(overlay_census.take().ok_or("W3 overlay census is absent")?)
            .map_err(|error| format!("W3 overlay did not return: {}", describe(&error)))?;
        overlay_return = Some(returned.clone());
        cultivated_potential = overlay
            .passage
            .read_terminal(&returned)
            .map_err(|error| format!("W3 cultivated potential return: {}", describe(&error)))?;
    }

    let receiver_faces = (receiver_option == ReceiverOption::Complete).then(|| ReceiverFaces {
        layers: receiver_layers,
        final_normed: final_normed.clone(),
        potential: potential.clone(),
    });

    // The container has not moved under the deed.
    source
        .verify_stable()
        .map_err(|e| format!("the container moved under the circulation: {e}"))?;
    if source.source_identity() != identity_before {
        return Err("the container's identity moved under the circulation".to_owned());
    }

    // The §5.4 key, composed from what this circulation actually holds. Nothing is hashed and
    // nothing is invented: the mode is the surface's, the source is the occurrence's container, the
    // topology is every segment's own census, the ports are the extents this input closure sizes
    // every kernel by, and the reductions are the first segment's coupling plans verbatim.
    let graph_key = GraphKey {
        mode: format!("{:?}", surface.mode()),
        source: source.source_identity(),
        topology: receipts
            .iter()
            .map(|r| (r.operations, r.fronts, r.graph_nodes, r.graph_edges))
            .collect(),
        ports: vec![
            ("continuing standing".to_owned(), model_rows, tower::HIDDEN),
            ("per-layer section".to_owned(), model_rows, tower::PLE_WIDTH),
            ("gated passage chart".to_owned(), model_rows, tower::FFN),
            (
                "potential section".to_owned(),
                match receiver_option {
                    ReceiverOption::Terminal => 1,
                    ReceiverOption::Complete => model_rows,
                },
                tower::VOCABULARY,
            ),
        ],
        grain: grain.0,
        series_terms: terms.0,
        reductions,
        receiver_boundary: match receiver_option {
            ReceiverOption::Terminal => format!(
                "the declared terminal of each segment ({} layer returns and one potential section); no other face was declared, which is why every seal factored",
                receipts.len() - 1
            ),
            ReceiverOption::Complete => format!(
                "the complete receiver: per-layer PLE/contact/enclosure, final normed standing, and potential ({} layer returns)",
                receipts.len() - 1
            ),
        },
        // The residency this circulation's executables baked in: the final deed's carried standing
        // is the one addressed section that is not the pool's, and the pool's own addresses are
        // fixed for the whole circulation. One tower, so no second deed contends for it — which is
        // exactly why H4 could not have found this field, and H5's cohort is where it is exercised.
        // H4 declares no chronology on its key: the circulation holds 43 diagrams and drops each
        // as it launches, so the names are not retained here. Deed H5's cohort retains them,
        // because a cohort is where two deeds share every count and differ by one occurrence.
        chronology: Vec::new(),
        material: material
            .standings
            .iter()
            .map(|(name, (section, _))| {
                (
                    name.clone(),
                    section.ranges()[0].0,
                    section.rows(),
                    section.width(),
                )
            })
            .collect(),
    };

    let census_after = surface.census();
    circulation.close();
    let stream_receipt = streamed.clone();
    let base = Circulated {
        tokens: tokens.to_vec(),
        segments: receipts,
        potential,
        final_normed,
        tower_work,
        streamed,
        census_before,
        census_after_tower,
        census_after,
        census_at_loop_open,
        census_at_loop_close,
        peak_charged_octets,
        wall_s: clock.elapsed().as_secs_f64(),
        loop_wall_s,
        admission,
        deed_launches,
        obstructions,
        terminal_refusal,
        graph_key,
        final_normed_bound,
        potential_bound,
        receiver: receiver_option,
        receiver_faces,
        tower_admission: tower_admission_receipt(tower_deeds)?,
    };
    if cultivation.is_some() {
        let overlay_work = overlay_work.ok_or("W3 overlay work receipt is absent")?;
        let overlay_apparatus =
            overlay_apparatus.ok_or("W3 overlay apparatus receipt is absent")?;
        let overlay_admission =
            overlay_admission.ok_or("W3 overlay deed admission receipt is absent")?;
        let overlay_execution =
            overlay_execution.ok_or("W3 overlay execution identity is absent")?;
        let overlay_return = overlay_return.ok_or("W3 overlay passage return receipt is absent")?;
        let pre_admission = pre_admission.ok_or("W3 pre-admission receipt is absent")?;
        let overlay_kernels_written = overlay_return.fronts.iter().all(|front| {
            front
                .readings
                .iter()
                .all(|reading| reading.measured.written && reading.measured.refused == 0)
                && front
                    .couplings
                    .iter()
                    .all(|coupling| coupling.written && coupling.refused == 0)
        });
        let overlay_census_refusals = overlay_return
            .fronts
            .iter()
            .flat_map(|front| {
                front
                    .readings
                    .iter()
                    .map(|reading| u64::from(reading.measured.refused))
            })
            .sum();
        let factor_material_reconciliation = pre_admission.factor_material_reconciliation.clone();
        let overlay_graph_identity = pre_admission.overlay_graph_identity.clone();
        let total_work = base.tower_work.then(&overlay_work);
        let total_deed_launches = base.deed_launches + overlay_execution.deed_launches;
        let terminal_synchronizations = stream_receipt.terminal_synchronizations;
        let resident_transfer_before = base.census_before.clone();
        let resident_transfer_after = base.census_after.clone();
        let memory_at_mount = surface.memory_at_mount();
        let memory_at_return = surface.memory().map_err(|error| error.to_string())?;
        let wall_seconds = format!("{:.9}", base.wall_s);
        let loop_wall_seconds = format!("{:.9}", base.loop_wall_s);
        Ok(CirculationOutput::Cultivated(CultivatedCirculated {
            base,
            base_potential_digest,
            cultivated_potential,
            overlay_work,
            overlay_apparatus,
            total_work,
            overlay_launches: overlay_execution.deed_launches,
            total_deed_launches,
            pre_admission,
            overlay_admission,
            overlay_return: overlay_return.clone(),
            overlay_fronts: overlay_return.fronts.clone(),
            overlay_kernels_written,
            overlay_census_refusals,
            factor_material_reconciliation,
            overlay_execution: overlay_execution.clone(),
            execution: streamed_cultivation::ExecutionReceipt {
                device_name: surface.device_name().to_owned(),
                mode: format!("{:?}", surface.mode()),
                kernel_sha256: surface.ptx_sha256().to_owned(),
                memory_at_mount_free: memory_at_mount.free_bytes as u64,
                memory_at_mount_total: memory_at_mount.total_bytes as u64,
                memory_at_return_free: memory_at_return.free_bytes as u64,
                memory_at_return_total: memory_at_return.total_bytes as u64,
                streamed: stream_receipt,
                resident_transfer_before,
                resident_transfer_after,
                overlay_transfer_before: overlay_return.census_before.clone(),
                overlay_transfer_after: overlay_return.census_after.clone(),
                terminal_synchronizations,
                wall_seconds,
                loop_wall_seconds,
                calibration: "CUDA driver device/memory/stream/transfer counters at this process aperture; clocks report and never admit".to_owned(),
                physical_energy: None,
                physical_utilization: None,
            },
            overlay_graph_identity,
            witness_stability_obligation: "the caller must verify the authenticated W3 witness at its owning rest boundary; OccurrenceWitness has no post-deed stability method",
        }))
    } else {
        Ok(CirculationOutput::Base(base))
    }
}
