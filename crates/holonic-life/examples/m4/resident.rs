//! Carry the held-out reflection word as one exact resident GPU graph.

use holonic_engine::embedding_fiber::{AlignedMaterial, ResidentReadout};
use holonic_engine::exact_work::ExactWork;
use holonic_engine::receiver_history_cultivation::MountedCultivatedHistory;
use holonic_engine::resident_section::{Dyadic, ResidentGrain, ResidentSurface, TransferCensus};
use num_traits::ToPrimitive;
use relational_geometry::Rat;
use serde::Serialize;

use super::quadric::MathematicalReturn;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentMathematicalReturn {
    pub device: String,
    pub ptx_sha256: String,
    pub graph: [usize; 6],
    pub occurrences: usize,
    pub captured_kernel_launches: u64,
    pub graph_deed_launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_section_octets: u64,
    pub host_egress_receipt_octets: u64,
    pub device_to_device_octets: u64,
    pub resident_octets_peak: u64,
    pub semantic_work: ExactWork,
    pub returned_words: Vec<i64>,
    pub exact_intervals_collapsed_to_points: bool,
    pub matches_source_detached_exact_control: bool,
    pub cpu_semantic_cells: usize,
}

pub fn conduct(
    mounted: &MountedCultivatedHistory,
    mathematical: &MathematicalReturn,
) -> Result<ResidentMathematicalReturn, String> {
    let conduct_order = &mathematical.held_out_conduct_order;
    if conduct_order.is_empty() {
        return Err("the held-out reflection word is empty".to_owned());
    }
    let readout = ResidentReadout::new().map_err(debug)?;
    let surface = ResidentSurface::on(&readout).map_err(display)?;
    let census_start = surface.census();
    let orbit = rest_orbit_factors(mounted)?;
    let factors = conduct_order
        .iter()
        .map(|member| {
            let (left, right) = orbit
                .get(*member)
                .ok_or_else(|| format!("orbit member {member} is outside the cultivated family"))?;
            let left = readout.mount(&aligned(left), 1).map_err(debug)?;
            let right = readout.mount(&aligned(right), right.len()).map_err(debug)?;
            Ok((left, right))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let input_integers = mathematical
        .held_out_input
        .iter()
        .map(rational_integer)
        .collect::<Result<Vec<_>, _>>()?;
    let stored_words = input_integers
        .iter()
        .copied()
        .map(encode_bfloat16_integer)
        .collect::<Result<Vec<_>, _>>()?;
    let width = input_integers.len();
    let grain = ResidentGrain(0);
    let staged = surface
        .stage_words(&stored_words, 1, width)
        .map_err(display)?;
    let enter_shape = surface
        .shape_enter(1, width, Dyadic::ONE, grain, &stored_words)
        .map_err(display)?;
    let entered = surface.fresh_section(1, width, grain).map_err(display)?;
    let mut factor_shapes = Vec::with_capacity(factors.len());
    let mut reentry_shapes = Vec::with_capacity(factors.len());
    let mut deltas = Vec::with_capacity(factors.len());
    let mut states = Vec::with_capacity(factors.len());
    let mut predecessor_octaves = enter_shape.needed;
    let mut semantic_work = enter_shape.predicted.clone();
    for (left, right) in &factors {
        let factor_shape = surface
            .shape_factorized_contract(1, width, predecessor_octaves, left, right, 1)
            .map_err(display)?;
        let reentry_shape = surface
            .shape_re_entry(1, width, predecessor_octaves, factor_shape.needed)
            .map_err(display)?;
        semantic_work = semantic_work
            .then(&factor_shape.predicted)
            .then(&reentry_shape.predicted);
        predecessor_octaves = reentry_shape.needed;
        factor_shapes.push(factor_shape);
        reentry_shapes.push(reentry_shape);
        deltas.push(surface.fresh_section(1, width, grain).map_err(display)?);
        states.push(surface.fresh_section(1, width, grain).map_err(display)?);
    }

    let mut declared = vec![Vec::new()];
    let mut prior_node = 0usize;
    for _ in conduct_order {
        let factor_node = declared.len();
        declared.push(vec![prior_node]);
        let reentry_node = declared.len();
        declared.push(vec![prior_node, factor_node]);
        prior_node = reentry_node;
    }
    let mut builder = surface.begin_passage(&declared).map_err(display)?;
    let lane = builder.open(0, &[]).map_err(display)?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &entered)
        .map_err(display)?;
    builder
        .close(0, &entered, enter_shape.needed)
        .map_err(display)?;
    for at in 0..factors.len() {
        let factor_node = 1 + 2 * at;
        let reentry_node = factor_node + 1;
        let predecessor = if at == 0 { &entered } else { &states[at - 1] };
        let lane = builder
            .open(factor_node, &declared[factor_node])
            .map_err(display)?;
        surface
            .record_factorized_contract(
                &lane,
                predecessor,
                &factors[at].0,
                &factors[at].1,
                &factor_shapes[at],
                &deltas[at],
            )
            .map_err(display)?;
        builder
            .close(factor_node, &deltas[at], factor_shapes[at].needed)
            .map_err(display)?;
        let lane = builder
            .open(reentry_node, &declared[reentry_node])
            .map_err(display)?;
        surface
            .record_re_entry(&lane, predecessor, &deltas[at], &states[at])
            .map_err(display)?;
        builder
            .close(reentry_node, &states[at], reentry_shapes[at].needed)
            .map_err(display)?;
    }
    let passage = builder.finish().map_err(display)?;
    let graph = passage.graph_census();
    let graph_receipt = [
        graph.nodes,
        graph.edges,
        graph.kernel_nodes,
        graph.memset_nodes,
        graph.memcpy_nodes,
        graph.other_nodes,
    ];
    let occurrences = passage.occurrences();
    let reading = passage.launch().map_err(display)?;
    if !reading.obstruction.is_empty() {
        return Err(format!(
            "the resident held-out word refused: {:?}",
            reading.obstruction.refusals
        ));
    }
    let intervals = surface
        .read_out(states.last().expect("held-out word has a terminus"))
        .map_err(display)?;
    let exact_intervals_collapsed_to_points = intervals.iter().all(|(lower, upper)| lower == upper);
    if !exact_intervals_collapsed_to_points {
        return Err("the integral reflection word returned a non-point enclosure".to_owned());
    }
    let returned_words = intervals
        .iter()
        .map(|interval| interval.0)
        .collect::<Vec<_>>();
    let expected = mathematical
        .held_out_output
        .iter()
        .map(rational_integer)
        .collect::<Result<Vec<_>, _>>()?;
    let matches_source_detached_exact_control = returned_words == expected;
    if !matches_source_detached_exact_control {
        return Err(
            "the resident reflection word disagrees with the detached exact control".into(),
        );
    }
    let census_end = surface.census();
    let delta = census_delta(&census_start, &census_end);
    Ok(ResidentMathematicalReturn {
        device: surface.device_name().to_owned(),
        ptx_sha256: surface.ptx_sha256().to_owned(),
        graph: graph_receipt,
        occurrences,
        captured_kernel_launches: delta.captured_launches,
        graph_deed_launches: delta.deed_launches,
        synchronizations: delta.synchronizations,
        host_ingress_octets: delta.ingress_octets,
        host_egress_section_octets: delta.egress_section_octets,
        host_egress_receipt_octets: delta.egress_receipt_octets,
        device_to_device_octets: delta.device_to_device_octets,
        resident_octets_peak: census_end.resident_octets_peak,
        semantic_work,
        returned_words,
        exact_intervals_collapsed_to_points,
        matches_source_detached_exact_control,
        cpu_semantic_cells: 0,
    })
}

fn rest_orbit_factors(
    mounted: &MountedCultivatedHistory,
) -> Result<Vec<(Vec<i64>, Vec<i64>)>, String> {
    let morphology = &mounted.rest().morphology;
    let mut left = morphology
        .left
        .iter()
        .map(rational_integer)
        .collect::<Result<Vec<_>, _>>()?;
    let mut right = morphology
        .right
        .iter()
        .map(rational_integer)
        .collect::<Result<Vec<_>, _>>()?;
    let seed = (left.clone(), right.clone());
    let mut returned = Vec::new();
    loop {
        if returned
            .iter()
            .any(|member| member == &(left.clone(), right.clone()))
        {
            if (left, right) != seed {
                return Err("the rested coordinate morphology did not close at its seed".to_owned());
            }
            break;
        }
        returned.push((left.clone(), right.clone()));
        left = morphology
            .coordinate_transport
            .iter()
            .map(|source| left[*source])
            .collect();
        right = morphology
            .coordinate_transport
            .iter()
            .map(|source| right[*source])
            .collect();
    }
    if returned.len() != mounted.receipt().orbit_extent {
        return Err("the rested factor orbit disagrees with its adjoint receipt".to_owned());
    }
    Ok(returned)
}

fn aligned(values: &[i64]) -> AlignedMaterial {
    AlignedMaterial {
        entries: values.to_vec(),
        exponent: 0,
        entry_octaves: values
            .iter()
            .map(|value| i64::BITS - value.unsigned_abs().leading_zeros())
            .max()
            .unwrap_or(0),
        negatives: values.iter().filter(|value| **value < 0).count() as u64,
    }
}

fn rational_integer(value: &Rat) -> Result<i64, String> {
    if value.denom() != &1.into() {
        return Err(format!("{value} is not an integral held-out coordinate"));
    }
    value
        .numer()
        .to_i64()
        .ok_or_else(|| format!("{value} leaves the signed resident word"))
}

/// Exact encoder for the integer subset of BF16 used at this exterior mouth.  It constructs bits
/// by shifts and verifies the engine's declared decoder returns the original integer.
fn encode_bfloat16_integer(value: i64) -> Result<u16, String> {
    if value == 0 {
        return Ok(0);
    }
    let negative = value < 0;
    let magnitude = value.unsigned_abs();
    let exponent = u64::BITS - 1 - magnitude.leading_zeros();
    let significand = if exponent <= 7 {
        magnitude << (7 - exponent)
    } else {
        let shift = exponent - 7;
        let lost_mask = (1u64 << shift) - 1;
        if magnitude & lost_mask != 0 {
            return Err(format!("integer {value} is not exact in BF16"));
        }
        magnitude >> shift
    };
    if !(128..=255).contains(&significand) {
        return Err(format!("integer {value} has an invalid BF16 significand"));
    }
    let exponent_field = exponent + 127;
    if exponent_field >= 255 {
        return Err(format!("integer {value} exceeds finite BF16"));
    }
    let sign = if negative { 1u16 << 15 } else { 0 };
    let word = sign | ((exponent_field as u16) << 7) | (significand as u16 - 128);
    let decoded = Dyadic::of_bfloat16_bits(word).map_err(display)?.value();
    if decoded != Rat::from_integer(value.into()) {
        return Err(format!(
            "BF16 mouth failed exact integer round trip for {value}"
        ));
    }
    Ok(word)
}

fn census_delta(before: &TransferCensus, after: &TransferCensus) -> TransferCensus {
    TransferCensus {
        ingress_octets: after.ingress_octets.saturating_sub(before.ingress_octets),
        egress_section_octets: after
            .egress_section_octets
            .saturating_sub(before.egress_section_octets),
        egress_receipt_octets: after
            .egress_receipt_octets
            .saturating_sub(before.egress_receipt_octets),
        device_to_device_octets: after
            .device_to_device_octets
            .saturating_sub(before.device_to_device_octets),
        captured_launches: after
            .captured_launches
            .saturating_sub(before.captured_launches),
        deed_launches: after.deed_launches.saturating_sub(before.deed_launches),
        control_launches: after
            .control_launches
            .saturating_sub(before.control_launches),
        synchronizations: after
            .synchronizations
            .saturating_sub(before.synchronizations),
        allocations: after.allocations.saturating_sub(before.allocations),
        resident_octets_now: after.resident_octets_now,
        resident_octets_peak: after.resident_octets_peak,
        section_read_outs: after
            .section_read_outs
            .saturating_sub(before.section_read_outs),
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
