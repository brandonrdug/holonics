//! M2's receiver-indexed active-transport return.
//!
//! This owner does not cluster activations and does not infer function from a foreign architecture
//! label.  It turns one already-conducted Phoenix cohort into (1) an ordered exact response
//! cochain, (2) receiver-visible supports and their first separators, (3) the pullback nerve founded
//! by exact resident-owner identity, and (4) separate apparatus, residency and realization faces.
//! Digests bind returned exact cells for audit; they never establish common transport.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::causal::EventId;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::interaction::PortHand;
use holonic_engine::phoenix::cohort::{Cohorted, LayerFace, TowerReturn};
use holonic_engine::phoenix::tower;
use serde::Serialize;
use sha2::{Digest, Sha256};

/// The M1 occurrence and ordered source word which enter the inherited body through an exterior
/// codec face.  The source occurrences, not the rendered bytes, retain the particle's lineage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExcitationPassage {
    pub occurrence: String,
    pub particle_occurrence: String,
    pub particle_word: Vec<EventId>,
    pub source_occurrences: BTreeSet<String>,
    pub generator_octets: Vec<u8>,
    pub exterior_codec_occurrence: String,
    pub codewords: Vec<usize>,
}

/// A face is addressed by chronology and local boundary ordinal.  `lineage` is a foreign
/// realization label retained for audit and prohibited from classifying the active cover.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ReceiverHistoryAddress {
    pub ordinal: usize,
    pub source_layer: Option<usize>,
    pub local_boundary_ordinal: usize,
    pub lineage: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResponseFaceReceipt {
    pub address: ReceiverHistoryAddress,
    pub cells: usize,
    pub exact_cells_sha256: String,
    /// True only where this suffix literally uses the base's prefix face instead of conducting a
    /// second occurrence.  It is not an equality measurement.
    pub inherited_from_base: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResponseCochain {
    pub occurrence: String,
    pub faces: Vec<ResponseFaceReceipt>,
}

/// A maximal half-open run of receiver cells satisfying the same exact predicate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct CellRun {
    pub start: usize,
    pub end: usize,
}

/// The first receiver cell at which two interval readings are disjoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CellSeparator {
    pub face: ReceiverHistoryAddress,
    pub cell: usize,
    pub base: (i64, i64),
    pub candidate: (i64, i64),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FaceDifference {
    pub face: ReceiverHistoryAddress,
    pub cells: usize,
    pub identical: usize,
    pub separated: usize,
    /// Different exact enclosures which still overlap at the declared grain.  They remain open;
    /// they are not silently thresholded into equality or separation.
    pub unresolved_overlap: usize,
    pub separated_support: Vec<CellRun>,
    pub unresolved_support: Vec<CellRun>,
    pub first_separator: Option<CellSeparator>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverVisibleSupport {
    pub differences: Vec<FaceDifference>,
    pub first_separator: Option<CellSeparator>,
    pub separated_faces: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum SwitchingCalibration {
    /// Graph/kernel/copy counts are apparatus acts, but transistor or SM switching was not sampled
    /// by a calibrated counter during this deed.
    Uncalibrated { obstruction: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ApparatusActivity {
    pub calibration: SwitchingCalibration,
    pub graph_launches: u64,
    pub terminal_synchronizations: u64,
    pub mount_launches: u64,
    pub mount_synchronizations: u64,
    pub asynchronous_copies: u64,
    pub asynchronous_copy_octets: u64,
    pub host_ingress_octets: u64,
    pub host_egress_section_octets: u64,
    pub resident_octets_peak: u64,
    pub pressure_partitions: Vec<PressurePartitionActivity>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PressurePartitionActivity {
    pub layer: usize,
    pub before_tower: usize,
    pub coordinate: String,
    pub required: String,
    pub former_ceiling: String,
}

/// A portable address for the exact shared standing.  Device ranges are apparatus testimony; the
/// source occurrence port plus owner/layer/population is the causal address.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ResidentStandingAddress {
    pub owner_tower: usize,
    pub released_after_layer: usize,
    pub population_lineage: String,
    pub source_event: EventId,
    pub source_port_ordinal: usize,
    pub source_port_hand: String,
    pub resident_ranges: [(u64, u64); 2],
    pub rows: usize,
    pub width: usize,
    pub bound: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PullbackLegAddress {
    pub standing: ResidentStandingAddress,
    pub receiving_event: EventId,
    pub receiving_port_ordinal: usize,
    pub receiving_port_hand: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidencyActivity {
    pub source_identity: String,
    pub peak_charged_octets: u64,
    pub admitted_resident_octets: u64,
    pub free_octets_at_admission: u64,
    pub prefix_pullback_legs: Vec<PullbackLegAddress>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RealizationPhase {
    pub receiver_history_ordinal: usize,
    pub source_layer: Option<usize>,
    pub operation_lineage: Vec<String>,
    pub intervention_occurrences: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RealizationPathParticipation {
    pub enters_at: usize,
    pub shared_prefix: bool,
    pub phases: Vec<RealizationPhase>,
}

/// One member of the active cover.  It is supported only by the response cochain and exact
/// receiver differences below; the declaration and operation names remain lineage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ActiveTransportOccurrence {
    pub occurrence: String,
    pub excitation_occurrence: String,
    pub tower: usize,
    pub declaration_lineage: String,
    pub cochain: ResponseCochain,
    pub realization: RealizationPathParticipation,
    pub support: ReceiverVisibleSupport,
    /// Exact semantic work of this complete source tower. Kept beside, never replaced by, launch
    /// and transfer telemetry so M3 can compare the complete source/native vector.
    pub exact_work: ExactWork,
}

/// An inhabited overlap cell: all listed branches pull back over this exact shared standing.
/// Higher cells are retained directly and are never reconstructed from pairwise edges.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ActiveOverlapNerveCell {
    pub standing: ResidentStandingAddress,
    pub branches: BTreeSet<usize>,
    pub receiving_occurrences: BTreeSet<(usize, EventId, usize)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UnchangedControl {
    pub occurrence: String,
    pub left: String,
    pub right: String,
    pub exact_faces_compared: usize,
    pub held: bool,
    pub first_separator: Option<CellSeparator>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenTransportFibre {
    pub occurrence: String,
    pub question: String,
    pub candidates: BTreeSet<String>,
    pub would_be_decided_by: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ActiveTransportFamily {
    pub occurrence: String,
    pub excitation: ExcitationPassage,
    pub apparatus: ApparatusActivity,
    pub residency: ResidencyActivity,
    pub responses: Vec<ActiveTransportOccurrence>,
    pub overlap_nerve: Vec<ActiveOverlapNerveCell>,
    pub unchanged_controls: Vec<UnchangedControl>,
    pub open_fibres: Vec<OpenTransportFibre>,
}

/// Exact transient response retained long enough to compare distinct source occurrences.  It is
/// deliberately not serializable as the M2 semantic receipt; the addressed native rest and
/// deterministic circulation remain its reconstruction route.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactResponseCochain {
    pub occurrence: String,
    pub faces: Vec<(ReceiverHistoryAddress, Vec<(i64, i64)>)>,
}

pub struct ReturnedActiveTransportFamily {
    pub receipt: ActiveTransportFamily,
    pub base_exact: ExactResponseCochain,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActiveTransportRefusal {
    EmptyExcitation,
    CodewordsDisagree,
    CohortHasNoBase,
    CohortHasNoReplay,
    FacePopulationDisagrees,
    ResponseChronologyDisagrees,
    PullbackOutsideTower(usize),
}

/// Return one excitation family.  Tower zero is the conducted base; tower one must be the whole
/// unchanged replay.  Every later tower is compared to the base under the same ordered receiver
/// family.
pub fn return_active_transport_family(
    excitation: ExcitationPassage,
    cohorted: &Cohorted,
) -> Result<ReturnedActiveTransportFamily, ActiveTransportRefusal> {
    if excitation.occurrence.is_empty()
        || excitation.particle_occurrence.is_empty()
        || excitation.particle_word.is_empty()
        || excitation.source_occurrences.is_empty()
        || excitation.generator_octets.is_empty()
        || excitation.exterior_codec_occurrence.is_empty()
        || excitation.codewords.is_empty()
    {
        return Err(ActiveTransportRefusal::EmptyExcitation);
    }
    if excitation.codewords != cohorted.tokens {
        return Err(ActiveTransportRefusal::CodewordsDisagree);
    }
    let base = cohorted
        .towers
        .first()
        .ok_or(ActiveTransportRefusal::CohortHasNoBase)?;
    let replay = cohorted
        .towers
        .get(1)
        .ok_or(ActiveTransportRefusal::CohortHasNoReplay)?;
    let base_exact = exact_cochain(format!("{}::tower-0", excitation.occurrence), base, base)?;

    let mut responses = Vec::with_capacity(cohorted.towers.len());
    for (tower_index, candidate) in cohorted.towers.iter().enumerate() {
        let exact = exact_cochain(
            format!("{}::tower-{tower_index}", excitation.occurrence),
            base,
            candidate,
        )?;
        let support = compare_exact(&base_exact, &exact)?;
        let cochain = receipt_of(&exact, base, candidate);
        responses.push(ActiveTransportOccurrence {
            occurrence: format!("{}::transport-{tower_index}", excitation.occurrence),
            excitation_occurrence: excitation.occurrence.clone(),
            tower: tower_index,
            declaration_lineage: candidate.declaration.name.clone(),
            cochain,
            realization: realization_of(candidate),
            support,
            exact_work: candidate.work.clone(),
        });
    }

    let replay_control = unchanged_control(
        format!("{}::whole-replay", excitation.occurrence),
        &base_exact,
        &exact_cochain(format!("{}::tower-1", excitation.occurrence), base, replay)?,
    )?;
    let overlap_nerve = overlap_nerve(cohorted)?;
    let residency = residency_of(cohorted)?;
    let apparatus = apparatus_of(cohorted);
    let mut open_fibres = Vec::new();
    for response in &responses {
        let unresolved = response
            .support
            .differences
            .iter()
            .filter(|difference| difference.unresolved_overlap > 0)
            .map(|difference| format!("receiver-history-{}", difference.face.ordinal))
            .collect::<BTreeSet<_>>();
        if !unresolved.is_empty() {
            open_fibres.push(OpenTransportFibre {
                occurrence: format!("{}::overlap-fibre", response.occurrence),
                question: "which finer receiver separates the unequal overlapping enclosures?"
                    .to_owned(),
                candidates: unresolved,
                would_be_decided_by: BTreeSet::from([
                    "a finer exact receiver grain".to_owned(),
                    "an admitted successor/intervention history".to_owned(),
                ]),
            });
        }
        if response.tower > 1 && response.support.first_separator.is_none() {
            open_fibres.push(OpenTransportFibre {
                occurrence: format!("{}::receiver-inert-fibre", response.occurrence),
                question: "does this intervention remain inert for all admitted successors?"
                    .to_owned(),
                candidates: BTreeSet::from([response.declaration_lineage.clone()]),
                would_be_decided_by: BTreeSet::from([
                    "a longer receiver history".to_owned(),
                    "a distinct M1 excitation occurrence".to_owned(),
                ]),
            });
        }
    }
    open_fibres.push(OpenTransportFibre {
        occurrence: format!("{}::switching-calibration-open", excitation.occurrence),
        question: "what calibrated physical switching field did this circulation induce?"
            .to_owned(),
        candidates: BTreeSet::from(["GPU switching remained unsampled".to_owned()]),
        would_be_decided_by: BTreeSet::from([
            "a calibrated aperture-bound hardware counter trace".to_owned()
        ]),
    });

    Ok(ReturnedActiveTransportFamily {
        receipt: ActiveTransportFamily {
            occurrence: format!("{}::active-transport-family", excitation.occurrence),
            excitation,
            apparatus,
            residency,
            responses,
            overlap_nerve,
            unchanged_controls: vec![replay_control],
            open_fibres,
        },
        base_exact,
    })
}

/// Exact unchanged control between two separately caused excitation occurrences.
pub fn unchanged_control(
    occurrence: impl Into<String>,
    left: &ExactResponseCochain,
    right: &ExactResponseCochain,
) -> Result<UnchangedControl, ActiveTransportRefusal> {
    let support = compare_exact(left, right)?;
    Ok(UnchangedControl {
        occurrence: occurrence.into(),
        left: left.occurrence.clone(),
        right: right.occurrence.clone(),
        exact_faces_compared: support.differences.len(),
        held: support
            .differences
            .iter()
            .all(|difference| difference.identical == difference.cells),
        first_separator: support.first_separator,
    })
}

fn exact_cochain(
    occurrence: String,
    base: &TowerReturn,
    candidate: &TowerReturn,
) -> Result<ExactResponseCochain, ActiveTransportRefusal> {
    let mut faces = Vec::with_capacity(tower::LAYERS * 3 + 2);
    for layer in 0..tower::LAYERS {
        let base_layer = base
            .layers
            .get(&layer)
            .ok_or(ActiveTransportRefusal::FacePopulationDisagrees)?;
        let face = candidate.layers.get(&layer).unwrap_or(base_layer);
        let start = faces.len();
        faces.push((
            address(start, Some(layer), 0, "per-layer input section"),
            face.ple.clone(),
        ));
        faces.push((
            address(start + 1, Some(layer), 1, "contact section"),
            face.contact.clone(),
        ));
        faces.push((
            address(start + 2, Some(layer), 2, "layer return"),
            face.terminal.clone(),
        ));
    }
    let ordinal = faces.len();
    faces.push((
        address(ordinal, None, 0, "final normed standing"),
        candidate.final_normed.clone(),
    ));
    faces.push((
        address(ordinal + 1, None, 1, "exterior potential section"),
        candidate.potential.clone(),
    ));
    Ok(ExactResponseCochain { occurrence, faces })
}

fn address(
    ordinal: usize,
    source_layer: Option<usize>,
    local_boundary_ordinal: usize,
    lineage: &str,
) -> ReceiverHistoryAddress {
    ReceiverHistoryAddress {
        ordinal,
        source_layer,
        local_boundary_ordinal,
        lineage: lineage.to_owned(),
    }
}

fn receipt_of(
    exact: &ExactResponseCochain,
    base: &TowerReturn,
    candidate: &TowerReturn,
) -> ResponseCochain {
    let faces = exact
        .faces
        .iter()
        .map(|(address, cells)| ResponseFaceReceipt {
            address: address.clone(),
            cells: cells.len(),
            exact_cells_sha256: exact_cells_digest(cells),
            inherited_from_base: address
                .source_layer
                .is_some_and(|layer| candidate.layers.get(&layer).is_none())
                && !std::ptr::eq(base, candidate),
        })
        .collect();
    ResponseCochain {
        occurrence: exact.occurrence.clone(),
        faces,
    }
}

fn compare_exact(
    base: &ExactResponseCochain,
    candidate: &ExactResponseCochain,
) -> Result<ReceiverVisibleSupport, ActiveTransportRefusal> {
    if base.faces.len() != candidate.faces.len() {
        return Err(ActiveTransportRefusal::ResponseChronologyDisagrees);
    }
    let mut differences = Vec::with_capacity(base.faces.len());
    let mut first_separator = None;
    for ((base_address, base_cells), (candidate_address, candidate_cells)) in
        base.faces.iter().zip(&candidate.faces)
    {
        if base_address != candidate_address || base_cells.len() != candidate_cells.len() {
            return Err(ActiveTransportRefusal::ResponseChronologyDisagrees);
        }
        let mut identical = 0usize;
        let mut separated_indices = Vec::new();
        let mut unresolved_indices = Vec::new();
        let mut face_first = None;
        for (cell, (left, right)) in base_cells.iter().zip(candidate_cells).enumerate() {
            if left == right {
                identical += 1;
            } else if disjoint(*left, *right) {
                separated_indices.push(cell);
                if face_first.is_none() {
                    face_first = Some(CellSeparator {
                        face: base_address.clone(),
                        cell,
                        base: *left,
                        candidate: *right,
                    });
                }
            } else {
                unresolved_indices.push(cell);
            }
        }
        if first_separator.is_none() {
            first_separator = face_first.clone();
        }
        differences.push(FaceDifference {
            face: base_address.clone(),
            cells: base_cells.len(),
            identical,
            separated: separated_indices.len(),
            unresolved_overlap: unresolved_indices.len(),
            separated_support: runs(&separated_indices),
            unresolved_support: runs(&unresolved_indices),
            first_separator: face_first,
        });
    }
    let separated_faces = differences
        .iter()
        .filter(|difference| difference.separated > 0)
        .count();
    Ok(ReceiverVisibleSupport {
        differences,
        first_separator,
        separated_faces,
    })
}

fn disjoint(left: (i64, i64), right: (i64, i64)) -> bool {
    left.1 < right.0 || right.1 < left.0
}

fn runs(indices: &[usize]) -> Vec<CellRun> {
    let mut out = Vec::new();
    let Some(&first) = indices.first() else {
        return out;
    };
    let mut start = first;
    let mut previous = first;
    for &index in &indices[1..] {
        if index != previous + 1 {
            out.push(CellRun {
                start,
                end: previous + 1,
            });
            start = index;
        }
        previous = index;
    }
    out.push(CellRun {
        start,
        end: previous + 1,
    });
    out
}

fn exact_cells_digest(cells: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    digest.update((cells.len() as u64).to_le_bytes());
    for (lower, upper) in cells {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    digest
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn realization_of(candidate: &TowerReturn) -> RealizationPathParticipation {
    let mut phases = Vec::new();
    for (layer, face) in &candidate.layers {
        phases.push(realization_phase(*layer * 3, Some(*layer), face));
    }
    phases.push(RealizationPhase {
        receiver_history_ordinal: tower::LAYERS * 3,
        source_layer: None,
        operation_lineage: candidate
            .final_operations
            .iter()
            .map(|(name, _)| name.clone())
            .collect(),
        intervention_occurrences: candidate
            .final_operations
            .iter()
            .filter(|(_, intervention)| *intervention)
            .count(),
    });
    RealizationPathParticipation {
        enters_at: candidate.declaration.enters_at,
        shared_prefix: candidate.declaration.shares_prefix,
        phases,
    }
}

fn realization_phase(
    receiver_history_ordinal: usize,
    source_layer: Option<usize>,
    face: &LayerFace,
) -> RealizationPhase {
    RealizationPhase {
        receiver_history_ordinal,
        source_layer,
        operation_lineage: face
            .operations
            .iter()
            .map(|(name, _)| name.clone())
            .collect(),
        intervention_occurrences: face
            .operations
            .iter()
            .filter(|(_, intervention)| *intervention)
            .count(),
    }
}

fn apparatus_of(cohorted: &Cohorted) -> ApparatusActivity {
    ApparatusActivity {
        calibration: SwitchingCalibration::Uncalibrated {
            obstruction: "no calibrated transistor/SM switching counter was sampled in this deed; launch and transfer counts remain separate apparatus projections".to_owned(),
        },
        graph_launches: cohorted.streamed.graph_launches,
        terminal_synchronizations: cohorted.streamed.terminal_synchronizations,
        mount_launches: cohorted.streamed.mount_launches,
        mount_synchronizations: cohorted.streamed.mount_synchronizations,
        asynchronous_copies: cohorted.streamed.asynchronous_copies,
        asynchronous_copy_octets: cohorted.streamed.asynchronous_copy_octets,
        host_ingress_octets: cohorted
            .census_after
            .ingress_octets
            .saturating_sub(cohorted.census_before.ingress_octets),
        host_egress_section_octets: cohorted
            .census_after
            .egress_section_octets
            .saturating_sub(cohorted.census_before.egress_section_octets),
        resident_octets_peak: cohorted.census_after.resident_octets_peak,
        pressure_partitions: cohorted
            .pressure_partitions
            .iter()
            .map(|partition| PressurePartitionActivity {
                layer: partition.layer,
                before_tower: partition.before_tower,
                coordinate: partition.coordinate.clone(),
                required: partition.required.clone(),
                former_ceiling: partition.former_ceiling.clone(),
            })
            .collect(),
    }
}

fn residency_of(cohorted: &Cohorted) -> Result<ResidencyActivity, ActiveTransportRefusal> {
    let mut legs = Vec::new();
    for receipt in &cohorted.prefix_pullbacks {
        if receipt.tower >= cohorted.towers.len() {
            return Err(ActiveTransportRefusal::PullbackOutsideTower(receipt.tower));
        }
        for leg in &receipt.legs {
            legs.push(PullbackLegAddress {
                standing: standing_address(&leg.standing),
                receiving_event: leg.sibling_entry.event,
                receiving_port_ordinal: leg.sibling_entry.ordinal,
                receiving_port_hand: hand(leg.sibling_entry.hand),
            });
        }
    }
    Ok(ResidencyActivity {
        source_identity: cohorted.source_identity.clone(),
        peak_charged_octets: cohorted.peak_charged_octets,
        admitted_resident_octets: cohorted.admission.prediction.resident_octets,
        free_octets_at_admission: cohorted.admission.free_octets_at_admission,
        prefix_pullback_legs: legs,
    })
}

fn overlap_nerve(
    cohorted: &Cohorted,
) -> Result<Vec<ActiveOverlapNerveCell>, ActiveTransportRefusal> {
    let mut cells = BTreeMap::<
        ResidentStandingAddress,
        (BTreeSet<usize>, BTreeSet<(usize, EventId, usize)>),
    >::new();
    for receipt in &cohorted.prefix_pullbacks {
        if receipt.tower >= cohorted.towers.len() {
            return Err(ActiveTransportRefusal::PullbackOutsideTower(receipt.tower));
        }
        for leg in &receipt.legs {
            let standing = standing_address(&leg.standing);
            let cell = cells.entry(standing).or_default();
            cell.0.insert(leg.standing.owner_tower);
            cell.0.insert(receipt.tower);
            cell.1.insert((
                receipt.tower,
                leg.sibling_entry.event,
                leg.sibling_entry.ordinal,
            ));
        }
    }
    Ok(cells
        .into_iter()
        .map(
            |(standing, (branches, receiving_occurrences))| ActiveOverlapNerveCell {
                standing,
                branches,
                receiving_occurrences,
            },
        )
        .collect())
}

fn standing_address(
    standing: &holonic_engine::phoenix::cohort::SharedStandingOccurrence,
) -> ResidentStandingAddress {
    ResidentStandingAddress {
        owner_tower: standing.owner_tower,
        released_after_layer: standing.released_after_layer,
        population_lineage: standing.population.clone(),
        source_event: standing.output.event,
        source_port_ordinal: standing.output.ordinal,
        source_port_hand: hand(standing.output.hand),
        resident_ranges: standing.resident_ranges,
        rows: standing.rows,
        width: standing.width,
        bound: standing.bound,
    }
}

fn hand(hand: PortHand) -> String {
    match hand {
        PortHand::Input => "input",
        PortHand::Output => "output",
    }
    .to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn face(ordinal: usize, values: &[(i64, i64)]) -> ExactResponseCochain {
        ExactResponseCochain {
            occurrence: format!("response-{ordinal}"),
            faces: vec![(
                address(ordinal, Some(0), 0, "lineage only"),
                values.to_vec(),
            )],
        }
    }

    #[test]
    fn disjoint_interval_is_a_separator_and_overlap_remains_open() {
        let base = face(0, &[(0, 2), (4, 5), (8, 9)]);
        let candidate = face(0, &[(1, 3), (6, 7), (8, 9)]);
        let support = compare_exact(&base, &candidate).expect("same chronology");
        assert_eq!(support.first_separator.as_ref().map(|s| s.cell), Some(1));
        assert_eq!(support.differences[0].separated, 1);
        assert_eq!(support.differences[0].unresolved_overlap, 1);
        assert_eq!(support.differences[0].identical, 1);
    }

    #[test]
    fn first_separator_respects_receiver_chronology_not_largest_change() {
        let base = ExactResponseCochain {
            occurrence: "base".to_owned(),
            faces: vec![
                (address(0, Some(0), 0, "first"), vec![(0, 0)]),
                (address(1, Some(0), 1, "second"), vec![(0, 0), (0, 0)]),
            ],
        };
        let candidate = ExactResponseCochain {
            occurrence: "candidate".to_owned(),
            faces: vec![
                (address(0, Some(0), 0, "first"), vec![(1, 1)]),
                (
                    address(1, Some(0), 1, "second"),
                    vec![(100, 100), (200, 200)],
                ),
            ],
        };
        let support = compare_exact(&base, &candidate).expect("same chronology");
        assert_eq!(
            support.first_separator.as_ref().map(|s| s.face.ordinal),
            Some(0)
        );
    }

    #[test]
    fn support_runs_are_lossless_and_not_a_scalar_magnitude() {
        assert_eq!(
            runs(&[1, 2, 4, 7, 8, 9]),
            vec![
                CellRun { start: 1, end: 3 },
                CellRun { start: 4, end: 5 },
                CellRun { start: 7, end: 10 },
            ]
        );
    }
}
