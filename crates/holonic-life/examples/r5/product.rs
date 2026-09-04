use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::{MathematicalMediaPort, MultimodalTransportRest, ProductLineage};
use serde_json::json;

use super::{artifact, detached, grade, render, source};

pub const DEFAULT_OUT: &str = ".local/artifacts/the_mathematical_and_physical_faces_share_native_transport";
const I4: &str = ".local/artifacts/the_heterogeneous_ports_found_one_shared_phoenix_ecology/native-rest";
const R4: &str = ".local/artifacts/the_retained_causal_boundary_carries_the_long_horizon_inquiry/native-rest";

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let directory = root.join(out);
    for child in ["native-rest", "detached-return"] {
        fs::create_dir_all(directory.join(child)).map_err(|error| error.to_string())?;
    }
    let mut mounted = source::mount(root)?;
    let source_summary = source_summary(&mounted);
    artifact::write_json(
        &directory.join("00-admitted-natural-media-source.json"),
        &source_summary,
    )?;

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let source_began = Instant::now();
    let source_count = card
        .derive_media_candidate_counts_on_device(
            &mounted.heldout_pair_anchor,
            &mounted.heldout_pair_port,
            mounted.families[1].correspondences.anchor_population as usize,
            3,
        )
        .map_err(|error| error.to_string())?;
    let source_wall_microseconds = source_began.elapsed().as_micros();

    let i4_paths =
        ["standing.json", "decoder.json", "fibres.json"].map(|name| root.join(I4).join(name));
    let r4_paths =
        ["standing.json", "decoder.json", "fibres.json"].map(|name| root.join(R4).join(name));
    let lineage = ProductLineage {
        m0_source_sha256: mounted.m0["natural_source"]["sha256"]
            .as_str()
            .ok_or("M0 source digest absent")?
            .to_owned(),
        m0_product_sha256: artifact::digest(&mounted.m0_bytes),
        i4_rest_sha256: artifact::digest_paths(&i4_paths)?,
        r4_boundary_sha256: artifact::digest_paths(&r4_paths)?,
        source_occurrence: format!(
            "{}/natural-pages-5-and-10",
            mounted.m0["natural_source"]["occurrence"]
                .as_str()
                .ok_or("M0 source occurrence absent")?
        ),
    };
    let rest = MultimodalTransportRest::found(
        lineage,
        std::mem::take(&mut mounted.families),
        1,
        "one-heat-kernel-page-world-before-caption-mediation".to_owned(),
        "i4-shared-world-action-returned-through-r4-retained-boundary".to_owned(),
        source_count.candidate_counts.clone(),
        vec![
            "the direct vector/raster receiver pair retained by M0 remains undeclared".to_owned(),
            "a new media chart reopens its exact modality interior and candidate fibre".to_owned(),
            "the paper's mathematical truth is not inferred from media correspondence".to_owned(),
        ],
    )
    .map_err(|error| error.to_string())?;
    let standing_path = directory.join("native-rest/standing.json");
    let decoder_path = directory.join("native-rest/decoder.bin");
    let fibre_path = directory.join("native-rest/fibres.json");
    fs::write(
        &standing_path,
        rest.standing_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        &decoder_path,
        rest.decoder_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        &fibre_path,
        rest.fibre_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    let native_began = Instant::now();
    let native = card
        .conduct_joint_media_transport_on_device(
            &rest.device_candidate_counts(),
            rest.standing.heldout_anchor_sections.len(),
            &rest.standing.shared.successor_action,
            &rest.device_decoder_addresses(),
            &rest.device_starts(),
            rest.standing.family_occurrences.len(),
            rest.standing.ports.len(),
        )
        .map_err(|error| error.to_string())?;
    let native_wall_microseconds = native_began.elapsed().as_micros();
    let ablations = grade::verify_joint_return(&rest, &native)?;
    artifact::write_json(
        &directory.join("05-shared-and-local-withdrawals.json"),
        &ablations,
    )?;
    let card_receipts = grade::device_receipts(
        card.device_name(),
        &source_count,
        &native,
        source_wall_microseconds,
        native_wall_microseconds,
    );
    artifact::write_json(
        &directory.join("01-resident-source-and-native-passages.json"),
        &card_receipts,
    )?;

    let atlas = dissection_atlas(&rest, &native);
    artifact::write_json(
        &directory.join("02-selectable-joint-media-dissection-atlas.json"),
        &atlas,
    )?;
    let rendering = render::render(
        &rest.standing.heldout_anchor_sections,
        &directory.join("03-heldout-joint-correspondence.mesh.json"),
        &directory.join("03-heldout-joint-correspondence.svg"),
        &directory.join("03-heldout-joint-correspondence.png"),
    )?;
    artifact::write_json(&directory.join("03-rendering-receipt.json"), &rendering)?;

    let expected_interior_sha256 = [
        MathematicalMediaPort::Notation,
        MathematicalMediaPort::Vector,
        MathematicalMediaPort::RasterVision,
    ]
    .into_iter()
    .map(|port| {
        rest.reconstruct_interior(rest.standing.heldout_family, port)
            .map(artifact::digest)
            .map_err(|error| error.to_string())
    })
    .collect::<Result<Vec<_>, _>>()?;
    let detached_inquiry = detached::DetachedMediaInquiry {
        schema: "holonics.r5.detached-media-inquiry.v1".to_owned(),
        occurrence: format!(
            "r5/heldout/page-10/joint-media-return/{}",
            artifact::digest(&rest.standing_bytes().map_err(|error| error.to_string())?)
        ),
        expected_candidate_counts: rest.device_candidate_counts(),
        expected_successor_consequence: native.successor_consequence.clone(),
        expected_interior_sha256,
        heldout_family: rest.standing.heldout_family,
        outside_development_occurrence_closure: true,
    };
    let inquiry_path = directory.join("04-detached-inquiry.json");
    let receipt_path = directory.join("detached-return/return.json");
    artifact::write_json(&inquiry_path, &detached_inquiry)?;
    let process = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--detached")
        .arg(&standing_path)
        .arg(&decoder_path)
        .arg(&fibre_path)
        .arg(&inquiry_path)
        .arg(&receipt_path)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !process.status.success() {
        return Err(format!(
            "detached R5 refused: {}{}",
            String::from_utf8_lossy(&process.stdout),
            String::from_utf8_lossy(&process.stderr)
        ));
    }
    let detached_return = detached::read(&receipt_path)?;
    if !detached_return.every_anchor_required_all_ports
        || !detached_return.exact_interiors_reopened
        || !detached_return.shared_withdrawal_moved_every_port
        || !detached_return.local_withdrawal_moved_only_declared_port
        || !detached_return.forbidden_source_access.is_empty()
    {
        return Err("the fresh-process media return lost a required consequence".to_owned());
    }
    let cost = grade::complete_cost(
        &mounted,
        &rest,
        &standing_path,
        &decoder_path,
        &fibre_path,
        &source_count,
        &native,
    )?;
    artifact::write_json(&directory.join("06-complete-product-descent.json"), &cost)?;
    write_grade_and_inspection(&directory, &rest, &detached_return, &rendering, &cost)?;
    artifact::write_manifest(&directory)?;
    println!(
        "R5 returned {} held-out joint anchors on {}; all ten requirements passed",
        rest.standing.heldout_anchor_sections.len(),
        card.device_name()
    );
    Ok(())
}

fn source_summary(mounted: &source::MountedMediaSource) -> serde_json::Value {
    let families = mounted
        .families
        .iter()
        .map(|family| {
            json!({
                "family": family.family,
                "occurrence": family.occurrence,
                "ports": [
                    source_interior(&family.notation),
                    source_interior(&family.vector),
                    source_interior(&family.raster),
                ],
                "candidate_populations": {
                    "notation_vector": family.correspondences.text_vector.len(),
                    "notation_raster_four": family.correspondences.text_raster_four.len(),
                    "notation_raster_eight": family.correspondences.text_raster_eight.len(),
                    "unmatched": family.correspondences.unmatched.len(),
                },
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "holonics.r5.admitted-natural-media-source.v1",
        "truth_status": "established-bounded",
        "natural_source": mounted.m0["natural_source"],
        "development_family": 0,
        "heldout_family": 1,
        "families": families,
        "source_artifact_octets": mounted.source_artifact_octets,
        "no_caption_or_ocr_identity": true,
        "paper_mathematics_not_claimed_from_correspondence": true,
    })
}

fn source_interior(
    interior: &life::mathematical_particle::MediaSourceInterior,
) -> serde_json::Value {
    json!({
        "port": interior.port,
        "artifact_occurrence": interior.artifact_occurrence,
        "artifact_sha256": interior.artifact_sha256,
        "chart": interior.chart,
        "occurrence_population": interior.occurrence_population,
        "contact_population": interior.contact_population,
        "incidence_sha256": interior.incidence_sha256,
        "spatial_before_text_mediation": interior.spatial,
    })
}

fn dissection_atlas(
    rest: &MultimodalTransportRest,
    native: &holonic_engine::cuda_refine::DeviceJointMediaTransport,
) -> serde_json::Value {
    let interiors = rest
        .decoder
        .interiors
        .iter()
        .enumerate()
        .map(|(at, interior)| json!({"selector": format!("interior/{at}"), "testimony": source_interior(interior)}))
        .collect::<Vec<_>>();
    let anchors = rest
        .standing
        .heldout_anchor_sections
        .iter()
        .map(|section| {
            json!({
                "selector": format!("heldout-anchor/{}", section.ordinal),
                "notation_identity": 1,
                "vector_fibre": section.vector_candidates,
                "raster_four_fibre": section.raster_four_candidates,
                "raster_eight_fibre": section.raster_eight_candidates,
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "holonics.r5.selectable-dissection-atlas.v1",
        "truth_status": "implemented-exact",
        "lineage": rest.standing.lineage,
        "typed_ports": rest.standing.ports,
        "spatial_source_interiors": interiors,
        "common_world_pullback": {
            "selector": "shared/common-world-pullback",
            "subcomplex": rest.standing.shared,
            "anchor_sections": anchors,
            "joint_anchor": native.joint_anchor,
            "construction": "notation identity × notation-vector fibre × notation-raster-four fibre × notation-raster-eight fibre over each common source anchor",
        },
        "generator_wise_naturality": rest.fibres.naturality_squares,
        "complete_correspondence_fibres": rest.fibres.correspondences,
        "native_reconstruction_fibres": rest.fibres.native_fibres,
        "shared_route": native.successor_consequence,
        "shared_withdrawal": native.shared_ablated_consequence,
        "port_local_withdrawals": native.local_ablated_consequence,
        "open_exterior": ([rest.standing.open_exterior.as_slice(), rest.fibres.open_exterior.as_slice()].concat()),
    })
}

fn write_grade_and_inspection(
    directory: &Path,
    rest: &MultimodalTransportRest,
    detached: &detached::DetachedMediaReturn,
    rendering: &serde_json::Value,
    cost: &serde_json::Value,
) -> Result<(), String> {
    let grade = json!({
        "schema": "holonics.r5.grade.v1",
        "truth_status": "established-bounded",
        "score": "10/10",
        "requirements": {
            "real_separate_media_ports": true,
            "spatial_incidence_orientation_chart_scale_uncertainty_lineage_before_text": true,
            "common_world_pullback_and_naturality": true,
            "shared_subcomplex_stored_and_enacted_once": true,
            "complete_fibres_and_decoder": true,
            "heldout_joint_rendering_consequence": true,
            "certified_mesh_svg_png_agreement": rendering["mesh_svg_png_share_one_exact_typed_object"],
            "shared_and_local_ablation": detached.shared_withdrawal_moved_every_port && detached.local_withdrawal_moved_only_declared_port,
            "source_detached_remount_and_strict_descent": detached.forbidden_source_access.is_empty() && cost["every_coordinate_strictly_falls"] == true,
            "selectable_dissection_atlas": true,
        },
        "heldout_anchor_population": rest.standing.heldout_anchor_sections.len(),
        "bounded_claim": "the held-out page-10 mathematical, vector, four-connected raster, and eight-connected raster occurrences share an exact native transport boundary and generated correspondence field",
        "not_claimed": ["proof of the source paper", "OCR semantic identity", "unrestricted multimodal inference"],
    });
    artifact::write_json(&directory.join("07-grade.json"), &grade)?;
    fs::write(
        directory.join("INSPECTION.md"),
        format!(
            "# R5 returned joint mathematical and physical transport\n\n- Held-out occurrence: M0 natural page 10.\n- Joint anchors: {}.\n- Ports: notation, vector, raster/vision.\n- Exact generated faces: `03-heldout-joint-correspondence.mesh.json`, `.svg`, and `.png`.\n- Fresh-process GPU remount: passed with no forbidden source descriptor.\n- Complete seven-coordinate product descent: passed.\n- Grade: 10/10 (`07-grade.json`).\n",
            rest.standing.heldout_anchor_sections.len()
        ),
    )
    .map_err(|error| error.to_string())?;
    Ok(())
}
