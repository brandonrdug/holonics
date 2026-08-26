use std::fs;
use std::path::Path;

use holonic_engine::cuda_refine::DeviceRaggedNativeTrace;
use holonic_engine::interchange::{certify_footprints, FrontCertificate, MemberFootprint};
use holonic_engine::receiver_exact_compression::ItemId;
use life::mathematical_particle::LongHorizonRetainedBoundary;
use serde_json::{json, Value};

use super::{
    detached::DetachedBoundaryReturn,
    source::{InquiryFront, PassageInputs},
};

pub fn endpoint(returned: &DeviceRaggedNativeTrace, front: usize) -> Result<u32, String> {
    let after = returned
        .trace_offsets
        .get(front + 1)
        .copied()
        .ok_or("trace boundary absent")? as usize;
    returned
        .native_trace
        .get(after.checked_sub(1).ok_or("empty trace interval")?)
        .copied()
        .ok_or("trace endpoint absent".to_owned())
}

pub fn verify_factorization(
    boundary: &LongHorizonRetainedBoundary,
    passages: &PassageInputs,
    source: &DeviceRaggedNativeTrace,
    uncondensed: &DeviceRaggedNativeTrace,
    compact: &DeviceRaggedNativeTrace,
) -> Result<Value, String> {
    let mut factors = Vec::new();
    for (front, (_, after)) in passages.source_front_task_ranges.iter().enumerate() {
        let source_task = after.checked_sub(1).ok_or("source replay front is empty")?;
        let source_endpoint = ItemId(u64::from(endpoint(source, source_task)?));
        let uncondensed_endpoint = ItemId(u64::from(endpoint(uncondensed, front)?));
        let source_native = boundary
            .native_of_source(source_endpoint)
            .map_err(|error| error.to_string())?;
        let uncondensed_native = boundary
            .native_of_source(uncondensed_endpoint)
            .map_err(|error| error.to_string())?;
        let compact_native = endpoint(compact, front)?;
        if source_native != uncondensed_native || source_native.0 as u32 != compact_native {
            return Err(format!(
                "front {front} does not factor through the retained boundary"
            ));
        }
        factors.push(json!({
            "front": front,
            "source_replay_endpoint": source_endpoint,
            "uncondensed_endpoint": uncondensed_endpoint,
            "factored_native_endpoint": source_native,
            "compact_endpoint": compact_native,
            "commutes": true,
        }));
    }
    Ok(json!({
        "fronts": factors,
        "every_declared_front_factors": true,
        "source_replay_auxiliary_prefix_returns_retained": source.front_count - factors.len(),
    }))
}

pub fn certify_interchange(
    returned: &DeviceRaggedNativeTrace,
    table_entries: u64,
) -> Result<FrontCertificate, String> {
    if returned.front_count < 3 || returned.trace_offsets.len() != returned.front_count + 1 {
        return Err("the independent front family is incomplete".to_owned());
    }
    let table_end = table_entries
        .checked_mul(4)
        .ok_or("table address overflow")?;
    let output_base = table_end
        .checked_add(4096)
        .ok_or("output address overflow")?;
    let footprints = (0..3)
        .map(|front| {
            let from = output_base + u64::from(returned.trace_offsets[front]) * 4;
            let to = output_base + u64::from(returned.trace_offsets[front + 1]) * 4;
            MemberFootprint {
                reads: vec![(0, table_end)],
                writes: vec![(from, to)],
            }
        })
        .collect::<Vec<_>>();
    let certificate = certify_footprints(&footprints);
    if !certificate.is_interchangeable() {
        return Err(
            "the independent inquiry fronts share a mutable apparatus footprint".to_owned(),
        );
    }
    Ok(certificate)
}

#[allow(clippy::too_many_arguments)]
pub fn complete_cost(
    source_standing: &Path,
    source_decoder: &Path,
    source_fibres: &Path,
    uncondensed_standing: &Path,
    uncondensed_decoder: &Path,
    uncondensed_fibres: &Path,
    compact_standing: &Path,
    compact_decoder: &Path,
    compact_fibres: &Path,
    passages: &PassageInputs,
    fronts: &[InquiryFront],
    source: &DeviceRaggedNativeTrace,
    uncondensed: &DeviceRaggedNativeTrace,
    compact: &DeviceRaggedNativeTrace,
) -> Result<Value, String> {
    let size = |path: &Path| -> Result<u64, String> {
        fs::metadata(path)
            .map(|metadata| metadata.len())
            .map_err(|error| error.to_string())
    };
    let source_span = passages
        .source_front_task_ranges
        .iter()
        .zip(fronts)
        .map(|((first, after), front)| after - first + front.word.len())
        .max()
        .unwrap_or(0) as u64;
    let compact_span = fronts
        .iter()
        .map(|front| front.word.len())
        .max()
        .unwrap_or(0) as u64;
    let source_transfer = source.host_ingress_octets + source.host_egress_octets;
    let uncondensed_transfer = uncondensed.host_ingress_octets + uncondensed.host_egress_octets;
    let compact_transfer = compact.host_ingress_octets + compact.host_egress_octets;
    let source_cost = json!({
        "artifact_octets": size(source_standing)?,
        "decoder_octets": size(source_decoder)?,
        "fibre_octets": size(source_fibres)?,
        "semantic_work": passages.source_words.len(),
        "dependency_span": source_span,
        "resident_octets": source.resident_octets,
        "transfer_octets": source_transfer,
    });
    let uncondensed_cost = json!({
        "artifact_octets": size(uncondensed_standing)?,
        "decoder_octets": size(uncondensed_decoder)?,
        "fibre_octets": size(uncondensed_fibres)?,
        "semantic_work": passages.compact_words.len(),
        "dependency_span": compact_span,
        "resident_octets": uncondensed.resident_octets,
        "transfer_octets": uncondensed_transfer,
    });
    let compact_cost = json!({
        "artifact_octets": size(compact_standing)?,
        "decoder_octets": size(compact_decoder)?,
        "fibre_octets": size(compact_fibres)?,
        "semantic_work": passages.compact_words.len(),
        "dependency_span": compact_span,
        "resident_octets": compact.resident_octets,
        "transfer_octets": compact_transfer,
    });
    let fell = |coordinate: &str| {
        source_cost[coordinate]
            .as_u64()
            .zip(compact_cost[coordinate].as_u64())
            .is_some_and(|(source, compact)| compact < source)
    };
    let coordinates = [
        "artifact_octets",
        "decoder_octets",
        "fibre_octets",
        "semantic_work",
        "dependency_span",
        "resident_octets",
        "transfer_octets",
    ];
    let strict = coordinates
        .iter()
        .map(|coordinate| ((*coordinate).to_owned(), Value::Bool(fell(coordinate))))
        .collect::<serde_json::Map<_, _>>();
    let every = strict.values().all(|value| value == true);
    Ok(json!({
        "schema": "holonics.r4.complete-product-descent.v1",
        "truth_status": "measured",
        "source_complete_replay": source_cost,
        "uncondensed_native_history": uncondensed_cost,
        "compact_retained_boundary": compact_cost,
        "strict_coordinate_fall": {
            "coordinates": strict,
            "every_coordinate_strictly_falls": every,
        },
        "decoder_and_fibre_are_included_not_externalized": true,
    }))
}

pub fn write_product_faces(
    directory: &Path,
    boundary: &LongHorizonRetainedBoundary,
    fronts: &[InquiryFront],
    detached: &DetachedBoundaryReturn,
) -> Result<(), String> {
    let holonomy = &boundary.standing.ordered_holonomy;
    let text = format!(
        "# The long-horizon inquiry returns through its retained causal boundary\n\nThe remote FamilySupport construction, its checked exterior constraint, its diagram incidence and its returned R3 cultivation are retained as addressed historical interiors rather than a summary string. The later proof, diagram and `n = 0` correction fronts each factor through one of {} native boundary states.\n\nThe richer exact-history receiver lawfully reopens a prior fibre. The detached process reconstructed {} octets with SHA-256 `{}` while the source fixtures and predecessor products were absent.\n\nThe predecessor/successor words `{:?}` and `{:?}` return distinct endpoints `{:?}` and `{:?}`; their order is load-bearing, with commutator rank {}. Independent proof, diagram and correction fronts retain disjoint output footprints and commute as one co-present card front.\n\nThis is bounded to the declared source, receiver, successor and cultivation family. It is not a claim of unrestricted context or mathematics.\n",
        boundary.standing.native_states.len(),
        detached.reconstructed_history_octets,
        detached.reconstructed_history_sha256,
        holonomy.left_word,
        holonomy.right_word,
        holonomy.left_endpoint,
        holonomy.right_endpoint,
        holonomy.commutator_rank,
    );
    fs::write(directory.join("11-long-horizon-return.md"), text)
        .map_err(|error| error.to_string())?;
    fs::write(
        directory.join("11-front-family.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "holonics.r4.long-horizon-front-family.v1",
            "fronts": fronts,
            "remote_earlier_construction_is_a_declared_predecessor": true,
            "proof_diagram_and_boundary_correction_are_distinct_receivers": true,
        }))
        .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}
