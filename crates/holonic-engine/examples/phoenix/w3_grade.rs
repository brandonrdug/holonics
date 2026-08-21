//! Receiver grade for the source-detached W3 child return.

use super::streamed;
use super::streamed::streamed_cultivation::OverlayExecutionIdentity;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::front_passage::PassageReturn;
use holonic_engine::streamed_standing::{GraphKey, StreamedCensus};
use serde::Serialize;
use sha2::Digest;

#[derive(Clone, Debug, Serialize)]
pub struct ApparatusSummary {
    pub deed_octets: u64,
    pub charged_octets: u64,
    pub allocations: u64,
    pub grid_extent: u64,
    pub carrier_peak_octaves: u64,
}

#[derive(Clone, Debug)]
pub struct FaceReturn {
    pub base: Vec<(i64, i64)>,
    pub cultivated: Vec<(i64, i64)>,
    pub deeds: u64,
    pub terminal_syncs: u64,
    pub loop_readouts_unchanged: bool,
    pub token_rows: usize,
    pub admitted: bool,
    pub returned: bool,
    pub base_clear: bool,
    pub overlay_work: ExactWork,
    pub total_work: ExactWork,
    pub overlay_apparatus: ApparatusSummary,
    pub base_face_digest: String,
    pub factor_material_reconciled: bool,
    pub overlay_return: PassageReturn,
    pub overlay_kernels_written: bool,
    pub overlay_census_refusals: u64,
    pub overlay_execution: OverlayExecutionIdentity,
    pub overlay_front_count: usize,
    pub overlay_obstruction_count: usize,
    pub overlay_refusal_count: usize,
    pub reconciliation: Vec<(String, u64, u64)>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Grade {
    pub held_out_changed: bool,
    pub control_potential_equal: bool,
    pub development_strict: bool,
    pub development_target_strict: bool,
    pub rank_separator_distinct: bool,
    pub development_preterminal_equal: bool,
    pub heldout_preterminal_equal: bool,
    pub terminal_target_changed: bool,
    pub heldout_target_changed: bool,
    pub control_complete_equal: bool,
    pub foil_overlay_delta_separated: bool,
    pub four_deeds: bool,
    pub one_terminal_sync: bool,
    pub no_loop_cpu_reads: bool,
    pub product_stable: bool,
    pub held_out_terminal_only: bool,
    pub foil_separated: bool,
    pub all_returns_admitted: bool,
    pub codec_reused: bool,
    pub no_op_base: bool,
    pub ablation_base: bool,
}

pub fn from_circulated(value: streamed::CultivatedCirculated) -> FaceReturn {
    let returned = !value.cultivated_potential.is_empty();
    let cultivated = value.cultivated_potential;
    let factor_material_reconciled = !value.factor_material_reconciliation.is_empty()
        && value
            .factor_material_reconciliation
            .iter()
            .all(|(_, predicted, measured)| predicted == measured)
        && value
            .overlay_admission
            .cited_material
            .as_ref()
            .map(|admission| admission == &value.pre_admission.material_admission)
            .unwrap_or(false);
    let base_face_digest = format!(
        "{:x}",
        sha2::Sha256::digest(
            serde_json::to_vec(&value.base.potential).expect("potential is serializable")
        )
    );
    let overlay_front_count = value.overlay_return.fronts.len();
    let overlay_obstruction_count = value.overlay_return.obstruction.refusals.len();
    let overlay_refusal_count = value.overlay_return.refusals.len();
    FaceReturn {
        base: value.base.potential,
        cultivated,
        deeds: value.total_deed_launches,
        terminal_syncs: value.base.streamed.terminal_synchronizations,
        loop_readouts_unchanged: value.base.census_at_loop_open.section_read_outs
            == value.base.census_at_loop_close.section_read_outs
            && value.base.census_at_loop_open.egress_section_octets
                == value.base.census_at_loop_close.egress_section_octets,
        token_rows: value.base.tokens.len(),
        admitted: value.base.admission.is_admitted()
            && value.pre_admission.material_admission.is_admitted()
            && !value.overlay_admission.semantic.is_empty()
            && !value.overlay_admission.apparatus.is_empty()
            && value.overlay_admission.is_admitted(),
        returned,
        base_clear: value.base.obstructions.is_empty() && value.base.terminal_refusal.is_none(),
        overlay_work: value.overlay_work,
        total_work: value.total_work,
        overlay_apparatus: ApparatusSummary {
            deed_octets: value.overlay_apparatus.deed_octets,
            charged_octets: value.overlay_apparatus.charged_octets,
            allocations: value.overlay_apparatus.allocations,
            grid_extent: value.overlay_apparatus.grid_extent,
            carrier_peak_octaves: value.overlay_apparatus.carrier_peak_octaves,
        },
        base_face_digest,
        factor_material_reconciled,
        overlay_return: value.overlay_return,
        overlay_kernels_written: value.overlay_kernels_written,
        overlay_census_refusals: value.overlay_census_refusals,
        overlay_execution: value.overlay_execution,
        overlay_front_count,
        overlay_obstruction_count,
        overlay_refusal_count,
        reconciliation: value.factor_material_reconciliation,
    }
}

/// Grade a separate base-only no-op/ablation run against the cultivated circulation's returned
/// W2 base. The comparison is semantic and receipt-complete; clocks are not part of the grade.
#[derive(Clone, Debug, Serialize)]
pub struct BaseOnlyGrade {
    pub complete_equal: bool,
    pub token_equal: bool,
    pub segments_equal: bool,
    pub work_equal: bool,
    pub potential_equal: bool,
    pub final_normed_equal: bool,
    pub obstruction_equal: bool,
    pub bounds_equal: bool,
    pub peak_equal: bool,
    pub deed_equal: bool,
    pub streamed_consequence_equal: bool,
    pub graph_key_consequence_equal: bool,
    pub material_shape_equal: bool,
    pub admission_consequence_equal: bool,
    pub base_free_octets: u64,
    pub cultivated_free_octets: u64,
    pub capacity_difference: i128,
    pub capacity_order: &'static str,
    pub reuse_refused: String,
    pub moved_material: usize,
}

fn streamed_consequence_equal(base: &StreamedCensus, cultivated: &StreamedCensus) -> bool {
    // The overlay is launched directly on the conducting CUDA stream but is not a pooled segment:
    // it never calls `StreamedCirculation::conducted`, so this census remains the W2 path's exact
    // 43-segment apparatus return in both arms. The overlay launch has its own execution receipt.
    base == cultivated
}

fn material_shapes(key: &GraphKey) -> Vec<(String, usize, usize)> {
    key.material
        .iter()
        .map(|(name, _, rows, width)| (name.clone(), *rows, *width))
        .collect()
}

fn graph_key_consequence_equal(base: &GraphKey, cultivated: &GraphKey) -> bool {
    base.mode == cultivated.mode
        && base.source == cultivated.source
        && base.topology == cultivated.topology
        && base.chronology == cultivated.chronology
        && base.ports == cultivated.ports
        && base.grain == cultivated.grain
        && base.series_terms == cultivated.series_terms
        && base.reductions == cultivated.reductions
        && base.receiver_boundary == cultivated.receiver_boundary
        && material_shapes(base) == material_shapes(cultivated)
}

fn segment_receipts_equal(
    base: &[streamed::SegmentReceipt],
    cultivated: &[streamed::SegmentReceipt],
) -> bool {
    base.len() == cultivated.len()
        && base.iter().zip(cultivated).all(|(left, right)| {
            left.layer == right.layer
                && left.slot == right.slot
                && left.maps == right.maps
                && left.species == right.species
                && left.role == right.role
                && left.operations == right.operations
                && left.fronts == right.fronts
                && left.graph_nodes == right.graph_nodes
                && left.graph_edges == right.graph_edges
                && left.captured_launches == right.captured_launches
                && left.seals_fused == right.seals_fused
                && left.seals_refused == right.seals_refused
                && left.quotients == right.quotients
                && left.collapsed_width_sum == right.collapsed_width_sum
                && left.collapsed_width_max == right.collapsed_width_max
                && left.collapsed_nonzero == right.collapsed_nonzero
                && left.lineage_empty == right.lineage_empty
                && left.a_priori_held == right.a_priori_held
                && left.every_front_certified == right.every_front_certified
                && left.deed == right.deed
                && left.material_resident_octets == right.material_resident_octets
        })
}

fn moved_material_population(base: &GraphKey, cultivated: &GraphKey) -> usize {
    base.material
        .iter()
        .zip(&cultivated.material)
        .filter(
            |(
                (left_name, left_address, left_rows, left_width),
                (right_name, right_address, right_rows, right_width),
            )| {
                left_name == right_name
                    && left_rows == right_rows
                    && left_width == right_width
                    && left_address != right_address
            },
        )
        .count()
}

pub fn grade_base_only(
    base_only: &streamed::Circulated,
    cultivated: &streamed::CultivatedCirculated,
) -> BaseOnlyGrade {
    let expected = &cultivated.base;
    let token_equal = base_only.tokens == expected.tokens;
    let segments_equal = segment_receipts_equal(&base_only.segments, &expected.segments);
    let work_equal = base_only.tower_work == expected.tower_work;
    let potential_equal = base_only.potential == expected.potential;
    let final_normed_equal = base_only.final_normed == expected.final_normed;
    let obstruction_equal = base_only.obstructions == expected.obstructions
        && base_only.terminal_refusal == expected.terminal_refusal;
    let bounds_equal = base_only.final_normed_bound == expected.final_normed_bound
        && base_only.potential_bound == expected.potential_bound;
    let peak_equal = base_only.peak_charged_octets == expected.peak_charged_octets;
    let deed_equal = base_only.deed_launches == expected.deed_launches;
    let streamed_equal = streamed_consequence_equal(&base_only.streamed, &expected.streamed);
    let graph_equal = graph_key_consequence_equal(&base_only.graph_key, &expected.graph_key);
    let material_shape_equal =
        material_shapes(&base_only.graph_key) == material_shapes(&expected.graph_key);
    let capacity_difference = i128::from(base_only.admission.free_octets_at_admission)
        - i128::from(expected.admission.free_octets_at_admission);
    let capacity_order = if capacity_difference < 0 {
        "base<cultivated"
    } else if capacity_difference > 0 {
        "base>cultivated"
    } else {
        "base=cultivated"
    };
    let reuse_refused = expected
        .graph_key
        .reuse_refused(&base_only.graph_key)
        .unwrap_or_else(|| {
            "no executable reuse refusal; addressed residency is identical".to_owned()
        });
    let moved_material = moved_material_population(&base_only.graph_key, &expected.graph_key);
    let admission_consequence_equal = base_only.admission.consequence_equal(&expected.admission);
    BaseOnlyGrade {
        complete_equal: token_equal
            && segments_equal
            && work_equal
            && potential_equal
            && final_normed_equal
            && obstruction_equal
            && bounds_equal
            && peak_equal
            && deed_equal
            && streamed_equal
            && graph_equal
            && material_shape_equal
            && admission_consequence_equal,
        token_equal,
        segments_equal,
        work_equal,
        potential_equal,
        final_normed_equal,
        obstruction_equal,
        bounds_equal,
        peak_equal,
        deed_equal,
        streamed_consequence_equal: streamed_equal,
        graph_key_consequence_equal: graph_equal,
        material_shape_equal,
        admission_consequence_equal,
        base_free_octets: base_only.admission.free_octets_at_admission,
        cultivated_free_octets: expected.admission.free_octets_at_admission,
        capacity_difference,
        capacity_order,
        reuse_refused,
        moved_material,
    }
}

pub fn grade(
    development: &FaceReturn,
    held_out: &FaceReturn,
    control: &FaceReturn,
    foil: &FaceReturn,
    derivation: &streamed::cultivation_overlay::RankDerivationReceipt,
    target: usize,
    product_stable: bool,
    codec_reused: bool,
    no_op_base: bool,
    ablation_base: bool,
) -> Result<Grade, String> {
    if development.token_rows == 0
        || held_out.token_rows == 0
        || control.token_rows == 0
        || foil.token_rows == 0
    {
        return Err("empty W3 terminal section".to_owned());
    }
    fn terminal<'a>(face: &'a [(i64, i64)], rows: usize) -> Result<&'a [(i64, i64)], String> {
        let start = rows
            .checked_sub(1)
            .and_then(|row| row.checked_mul(super::tower::VOCABULARY))
            .ok_or("terminal offset overflow")?;
        let end = start
            .checked_add(super::tower::VOCABULARY)
            .ok_or("terminal extent overflow")?;
        face.get(start..end)
            .ok_or_else(|| "potential terminal extent drifted".to_owned())
    }
    let dev_terminal = terminal(&development.cultivated, development.token_rows)?;
    let dev_base_terminal = terminal(&development.base, development.token_rows)?;
    let held_terminal = terminal(&held_out.cultivated, held_out.token_rows)?;
    let held_base_terminal = terminal(&held_out.base, held_out.token_rows)?;
    let foil_terminal = terminal(&foil.cultivated, foil.token_rows)?;
    let foil_base_terminal = terminal(&foil.base, foil.token_rows)?;
    let target_lower = dev_terminal
        .get(target)
        .map(|value| value.0)
        .ok_or_else(|| "development target is outside returned potential".to_owned())?;
    let competitor = dev_terminal
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != target)
        .map(|(_, value)| value.1)
        .max()
        .ok_or_else(|| "development has no strict competitor".to_owned())?;
    let held_prefix = held_out.token_rows.saturating_sub(1) * super::tower::VOCABULARY;
    let dev_prefix = development.token_rows.saturating_sub(1) * super::tower::VOCABULARY;
    let development_preterminal_equal =
        development.base.get(..dev_prefix) == development.cultivated.get(..dev_prefix);
    let heldout_preterminal_equal =
        held_out.base.get(..held_prefix) == held_out.cultivated.get(..held_prefix);
    let terminal_target_changed = dev_base_terminal.get(target) != dev_terminal.get(target);
    let heldout_target_changed = held_base_terminal.get(target) != held_terminal.get(target);
    let delta = |cultivated: &[(i64, i64)], base: &[(i64, i64)]| -> Option<(i64, i64)> {
        cultivated
            .get(target)
            .zip(base.get(target))
            .map(|(c, b)| (c.0 - b.0, c.1 - b.1))
    };
    let foil_overlay_delta_separated =
        delta(foil_terminal, foil_base_terminal) != delta(dev_terminal, dev_base_terminal);
    let rank_separator_distinct =
        derivation.separator.candidate != derivation.separator.predecessor;
    let development_target_strict = target_lower > competitor;
    let strict = development_target_strict && rank_separator_distinct;
    let telemetry = [development, held_out, control, foil];
    Ok(Grade {
        held_out_changed: held_base_terminal.get(target) != held_terminal.get(target),
        control_potential_equal: control.base == control.cultivated,
        development_strict: strict,
        development_target_strict,
        rank_separator_distinct,
        development_preterminal_equal,
        heldout_preterminal_equal,
        terminal_target_changed,
        heldout_target_changed,
        control_complete_equal: control.base == control.cultivated,
        foil_overlay_delta_separated,
        four_deeds: telemetry.iter().all(|value| value.deeds == 44),
        one_terminal_sync: telemetry.iter().all(|value| value.terminal_syncs == 1),
        no_loop_cpu_reads: telemetry.iter().all(|value| value.loop_readouts_unchanged),
        product_stable,
        held_out_terminal_only: heldout_preterminal_equal
            && heldout_target_changed
            && development_preterminal_equal,
        foil_separated: foil_overlay_delta_separated,
        all_returns_admitted: telemetry.iter().all(|value| {
            value.admitted
                && value.returned
                && value.base_clear
                && value.factor_material_reconciled
                && value.overlay_kernels_written
                && value.overlay_census_refusals == 0
                && !value.overlay_return.fronts.is_empty()
                && value.overlay_return.obstruction.is_empty()
                && value.overlay_return.refusals.is_empty()
                && value.overlay_execution.graph_nodes > 0
                && value.overlay_execution.graph_edges > 0
                && value.overlay_execution.captured_launches > 0
                && value.overlay_execution.graph_execs > 0
                && value.overlay_execution.deed_launches == 1
        }),
        codec_reused,
        no_op_base,
        ablation_base,
    })
}

impl Grade {
    pub fn passes(&self) -> bool {
        self.held_out_changed
            && self.held_out_terminal_only
            && self.control_potential_equal
            && self.control_complete_equal
            && self.development_preterminal_equal
            && self.heldout_preterminal_equal
            && self.terminal_target_changed
            && self.heldout_target_changed
            && self.development_target_strict
            && self.rank_separator_distinct
            && self.development_strict
            && self.four_deeds
            && self.one_terminal_sync
            && self.no_loop_cpu_reads
            && self.product_stable
            && self.foil_separated
            && self.foil_overlay_delta_separated
            && self.all_returns_admitted
            && self.codec_reused
            && self.no_op_base
            && self.ablation_base
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(material: Vec<(String, u64, usize, usize)>) -> GraphKey {
        GraphKey {
            mode: "mode".to_owned(),
            source: "source".to_owned(),
            topology: vec![(1, 1, 1, 1)],
            chronology: vec!["law".to_owned()],
            ports: vec![("p".to_owned(), 1, 1)],
            grain: 20,
            series_terms: 14,
            reductions: vec![("k".to_owned(), 1)],
            receiver_boundary: "terminal".to_owned(),
            material,
        }
    }

    #[test]
    fn an_overlay_launch_is_not_invented_inside_the_pooled_stream_census() {
        let base = StreamedCensus {
            graph_launches: 43,
            ..StreamedCensus::default()
        };
        let cultivated = base.clone();
        assert!(streamed_consequence_equal(&base, &cultivated));
        let invented_overlay = StreamedCensus {
            graph_launches: 44,
            ..cultivated.clone()
        };
        assert!(!streamed_consequence_equal(&base, &invented_overlay));
        let drift = StreamedCensus {
            pinned_octets: 1,
            ..cultivated
        };
        assert!(!streamed_consequence_equal(&base, &drift));
    }

    #[test]
    fn graph_key_comparison_accepts_address_relocation_but_refuses_shape_or_topology_drift() {
        let base = key(vec![("standing".to_owned(), 0x100, 2, 3)]);
        let relocated = key(vec![("standing".to_owned(), 0x200, 2, 3)]);
        assert!(graph_key_consequence_equal(&base, &relocated));
        assert_eq!(moved_material_population(&base, &relocated), 1);
        assert!(
            relocated
                .reuse_refused(&base)
                .is_some_and(|reason| reason.contains("RESIDENCY"))
        );
        let shape = key(vec![("standing".to_owned(), 0x200, 2, 4)]);
        assert!(!graph_key_consequence_equal(&base, &shape));
        let mut topology = relocated.clone();
        topology.topology.push((2, 2, 2, 2));
        assert!(!graph_key_consequence_equal(&base, &topology));
    }
}
