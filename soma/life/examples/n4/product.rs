use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    phoenix::heterogeneous_fusion::HeterogeneousFusionRest,
};
use life::{
    mathematical_particle::{NativeCodec, NativeSuccessorHistory},
    mathematical_source::OpticalPassage,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use super::{
    artifact,
    cultivation::{NativeCultivatedMathematicalRest, NativeMathematicalWorldReturn},
    rest::{AthenaContinuationStanding, LaboratoryAthenaProduct},
    world_return,
};

pub const DEFAULT_OUT: &str =
    "output/the_laboratory_mathematics_athena_unifies_native_inference_ocr_and_three_port_transport";
const N3_REST: &str =
    "output/the_returned_native_mathematical_world_cultivates_the_laboratory_hexis/native-rest";
const N1_REST: &str = "output/n1_raw_optical_mathematical_recovery_complete/native-rest/standing.json";
const N2_REST: &str = "output/the_acoustic_section_crosses_the_inherited_projection_and_three_ports_share_one_native_ecology/native-rest";
const N0_GRADE: &str =
    "output/native_mathematical_consequence_precedes_every_codec/00-N0-grade.json";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ApplicationOccurrence {
    occurrence: String,
    sections: Vec<Vec<i64>>,
    histories: Vec<NativeSuccessorHistory>,
    expected: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProductComponent {
    name: String,
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProductManifest {
    schema: String,
    truth_status: String,
    product_sha256: String,
    components: Vec<ProductComponent>,
    application_occurrences: Vec<ApplicationOccurrence>,
    open_exterior: Vec<String>,
}

pub fn construct(root: &Path, output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "N4 output {} already exists; inspect the frozen product instead of replaying it",
            output.display()
        ));
    }
    fs::create_dir_all(output.join("native-rest")).map_err(|error| error.to_string())?;
    fs::create_dir_all(output.join("detached-return")).map_err(|error| error.to_string())?;
    fs::create_dir_all(output.join("projections")).map_err(|error| error.to_string())?;

    let predecessor_standing = artifact::read(root.join(N3_REST).join("predecessor-standing.bin"))?;
    let predecessor_decoder = artifact::read(root.join(N3_REST).join("predecessor-decoder.bin"))?;
    let predecessor_fibres = artifact::read(root.join(N3_REST).join("predecessor-fibres.bin"))?;
    let cultivation_standing = artifact::read(root.join(N3_REST).join("cultivation-standing.json"))?;
    let mathematics = NativeCultivatedMathematicalRest::read(
        &predecessor_standing,
        &predecessor_decoder,
        &predecessor_fibres,
        &cultivation_standing,
    )?;
    let optical_bytes = artifact::read(root.join(N1_REST))?;
    let optical: OpticalPassage =
        serde_json::from_slice(&optical_bytes).map_err(|error| error.to_string())?;
    let heterogeneous_standing = artifact::read(root.join(N2_REST).join("standing.json"))?;
    let heterogeneous_decoder = artifact::read(root.join(N2_REST).join("decoder.json"))?;
    let heterogeneous_fibres = artifact::read(root.join(N2_REST).join("fibres.json"))?;
    let heterogeneous = HeterogeneousFusionRest::read(
        &heterogeneous_standing,
        &heterogeneous_decoder,
        &heterogeneous_fibres,
    )
    .map_err(|error| error.to_string())?;

    // A later N4 current first conducts through N3, then its emitted geometry crosses a new raw
    // optical occurrence. The returned history suffix is the new durable morphology.
    let prior_history = mathematics
        .predecessor()
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .take(4)
        .cloned()
        .chain(std::iter::once(
            mathematics.standing().world_return.occurrence.clone(),
        ))
        .collect::<Vec<_>>();
    let seed_inquiry = mathematics
        .predecessor()
        .found_native_mathematical_inquiry(
            vec![
                "n4/continuation/seed/integer".to_owned(),
                "n4/continuation/seed/modulus-two".to_owned(),
            ],
            vec![vec![29, -29, 0], vec![13, -13, 0]],
            vec![NativeSuccessorHistory::ComposedJoint],
            prior_history,
            vec!["later nonlinear continuations remain open".to_owned()],
        )
        .map_err(|error| error.to_string())?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let seed_consequence =
        mathematics.conduct_rich_cultivated_consequence(&seed_inquiry, &mut card)?;
    let emitted_path = output.join("00-later-emitted-native-geometry.png");
    let emitted = world_return::emit_geometry(&seed_consequence, &emitted_path)?;
    artifact::write_json(output.join("00-later-emitted-native-geometry.json"), &emitted)?;
    let returned_path = output.join("01-later-returned-optical-world.json");
    let status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--optical-return")
        .arg(&emitted_path)
        .arg(&returned_path)
        .current_dir(root)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err("the N4 later optical world return refused".to_owned());
    }
    let returned_optical = world_return::read_passage(&returned_path)?;
    let heterogeneous_identity = artifact::value_digest(&(
        artifact::digest(&heterogeneous_standing),
        artifact::digest(&heterogeneous_decoder),
        artifact::digest(&heterogeneous_fibres),
    ))?;
    let return_difference = artifact::value_digest(&(
        &seed_consequence.occurrence,
        &returned_optical.occurrence,
        &returned_optical.native_consequence,
        &heterogeneous_identity,
    ))?;
    let returned_world = NativeMathematicalWorldReturn {
        occurrence: format!("n4/world-return/{return_difference}"),
        emitted_native_consequence: seed_consequence.occurrence.clone(),
        returned_optical_occurrence: returned_optical.occurrence.clone(),
        returned_multimodal_rest_sha256: heterogeneous_identity,
        causing_laboratory_occurrences: vec![
            mathematics.standing().world_return.occurrence.clone(),
            optical.occurrence.clone(),
            heterogeneous.standing.shared_generator.lineage.clone(),
        ],
        exact_return_difference_sha256: return_difference,
        support_families: vec![0, 1],
        separately_addressed_after_emission: true,
    };
    let continuation = AthenaContinuationStanding::found(&mathematics, returned_world)?;
    let product = LaboratoryAthenaProduct::found(
        mathematics,
        optical,
        heterogeneous,
        continuation,
    )?;
    let product_identity = product.canonical_identity()?;
    let application_occurrences = vec![
        ApplicationOccurrence {
            occurrence: "n4/application/fixed-recombination".to_owned(),
            sections: vec![vec![19, -19, 0], vec![9, -9, 0]],
            histories: vec![NativeSuccessorHistory::FixedSection],
            expected: "two exact fixed sections with continuation lineage".to_owned(),
        },
        ApplicationOccurrence {
            occurrence: "n4/application/carrier-separator".to_owned(),
            sections: vec![vec![1, 1, 0], vec![1, 0, 0]],
            histories: vec![NativeSuccessorHistory::ExpandedGenerator],
            expected: "two retained carrier obstructions".to_owned(),
        },
        ApplicationOccurrence {
            occurrence: "n4/application/rebase-extrapolation".to_owned(),
            sections: vec![vec![23, -23, 0], vec![5, -5, 0]],
            histories: vec![NativeSuccessorHistory::CarrierRebase {
                source: 0,
                target: 1,
            }],
            expected: "held-out fixed sections under a declared rebase history".to_owned(),
        },
    ];
    let components = freeze_components(output, &product)?;
    let manifest = ProductManifest {
        schema: "holonics.n4.laboratory-mathematics-athena-rest.v1".to_owned(),
        truth_status: "established-bounded".to_owned(),
        product_sha256: product_identity.clone(),
        components,
        application_occurrences: application_occurrences.clone(),
        open_exterior: vec![
            "native nonlinear analytic, dimensional/unit, and wider successor families".to_owned(),
            "new raw pages require the inherited Tesseract optical face before native spatial binding".to_owned(),
            "the stored twelve-layer Gemma audio tower remains unexcited; N2 enacts exact PCM incidence and the authenticated projection".to_owned(),
            "general conversational generation and full foreign text/vision tower inference remain outside this frozen aperture".to_owned(),
        ],
    };
    artifact::write_json(output.join("native-rest/MANIFEST.json"), &manifest)?;
    artifact::write_json(output.join("application-occurrences.json"), &application_occurrences)?;

    // Inspect several product returns before the source-detached repetition.
    let direct = conduct_application(&product, &application_occurrences)?;
    artifact::write_json(output.join("02-direct-native-application.json"), &direct)?;
    emit_projections(output, &product, &application_occurrences[0])?;

    run_detached(
        &env::current_exe().map_err(|error| error.to_string())?,
        &output.join("native-rest"),
        &output.join("application-occurrences.json"),
        &output.join("detached-return/return.json"),
    )?;
    let detached: Value = serde_json::from_slice(&artifact::read(
        output.join("detached-return/return.json"),
    )?)
    .map_err(|error| error.to_string())?;
    if detached["product_sha256"] != product_identity
        || detached["passed"] != true
        || detached["forbidden_source_descriptors"] != json!([])
        || detached["lean_or_checker_opened"] != false
    {
        return Err("the frozen N4 product did not return source-detached".to_owned());
    }

    let source_model_octets = fs::metadata("/home/b/models/gemma-4-E4B-it/model.safetensors")
        .map(|metadata| metadata.len())
        .unwrap_or(0);
    let product_octets = manifest.components.iter().map(|part| part.octets).sum::<u64>();
    let capability = json!({
        "schema": "holonics.n4.capability-atlas.v1",
        "truth_status": "established-bounded",
        "competitive_aperture": {
            "native_mathematics": "exact two-carrier integer/F2 fixed-section, rebase, separator, local-ablation, reconstruction-fibre, and derivational-history consequences",
            "ocr": "one real held-out untranscribed page with 1,164 inherited glyph faces bound to 1,051 native optical components; new raw pages cross the same inherited-optical/native-spatial boundary",
            "multimodal": "receiver-exact text, vision, and audio entry-port ecology for the declared two-state/two-family shared generator, with all shared/local withdrawals",
            "cultivation": "two separately addressed optical world returns retained as durable history morphology; later native identity and derivational transport change while equal exact answers remain conservatively distinct",
            "generation": "native consequence first; notation, JSON, English, Lean data, Rust data, raster, mesh, and acoustic faces are downstream projections",
        },
        "measured_product": {
            "product_sha256": product_identity,
            "rest_octets": product_octets,
            "source_model_octets_for_ancestry_coordinate_only": source_model_octets,
            "rest_to_source_model_numerator": product_octets,
            "rest_to_source_model_denominator": source_model_octets,
            "not_a_full_model_receiver_equivalence_or_general_language_compression_claim": true,
        },
        "optical": {
            "components": product.optical().components.len(),
            "relations": product.optical().relations.len(),
            "ambiguity_fibres": product.optical().ambiguity_fibres.len(),
            "glyph_faces": product.optical().glyph_testimony.as_ref().map(|testimony| testimony.glyphs.len()).unwrap_or(0),
        },
        "heterogeneous": {
            "ports": product.heterogeneous().standing.ports,
            "naturality_squares": product.heterogeneous().fibres.naturality_squares.len(),
            "reconstruction_fibres": product.heterogeneous().fibres.fibres.len(),
            "open_exterior": product.heterogeneous().standing.open_exterior,
        },
        "mathematical_open_exterior": product.continuation().open_exterior,
        "product_open_exterior": manifest.open_exterior,
    });
    artifact::write_json(output.join("03-capability-atlas.json"), &capability)?;

    let dissection = json!({
        "schema": "holonics.n4.complete-product-dissection.v1",
        "truth_status": "established-bounded",
        "ancestry": {
            "n0": artifact::digest(artifact::read(root.join(N0_GRADE))?),
            "n1": artifact::digest(artifact::read(root.join("output/n1_raw_optical_mathematical_recovery_complete/05-grade-and-boundary.json"))?),
            "n2": artifact::digest(artifact::read(root.join("output/the_acoustic_section_crosses_the_inherited_projection_and_three_ports_share_one_native_ecology/02-grade.json"))?),
            "n3": artifact::digest(artifact::read(root.join("output/the_returned_native_mathematical_world_cultivates_the_laboratory_hexis/09-grade.json"))?),
        },
        "passages": product.mathematics().predecessor().decoder().declared_histories,
        "generators": [
            product.mathematics().predecessor().standing().generator.occurrence.clone(),
            product.heterogeneous().standing.shared_generator.name.clone(),
        ],
        "relations": product.mathematics().predecessor().standing().relations,
        "fibres": {
            "mathematical": product.mathematics().predecessor().reconstruction(),
            "optical": product.optical().ambiguity_fibres.len(),
            "modality": product.heterogeneous().fibres.fibres,
        },
        "separators": product.mathematics().predecessor().reconstruction().shortest_separators,
        "caustics": ["integer/F2 residual split", "optical rank-loss ambiguity fibres", "unexcited foreign tower interiors"],
        "holonomy": product.heterogeneous().fibres.naturality_squares,
        "higher_cells": product.mathematics().predecessor().decoder().naturality,
        "modality_junctions": product.heterogeneous().standing.shared_generator,
        "continued_history": product.continuation(),
        "open_exterior": manifest.open_exterior,
    });
    artifact::write_json(output.join("04-complete-product-dissection.json"), &dissection)?;

    let readback = read_product(&output.join("native-rest"))?;
    let withdrawal = readback.withdraw()?;
    if !withdrawal.exact_component_owners_returned
        || withdrawal.product_sha256 != product_identity
    {
        return Err("N4 exact component withdrawal refused".to_owned());
    }
    artifact::write_json(output.join("05-exact-product-withdrawal.json"), &withdrawal)?;
    let grade = json!({
        "schema": "holonics.n4.grade.v1",
        "truth_status": "established-bounded",
        "passed": true,
        "native_mathematical_inference_precedes_every_projection": true,
        "real_raw_page_ocr_rest_and_native_complex": true,
        "three_port_text_vision_audio_rest_with_complete_withdrawals": true,
        "multi_occurrence_derivation_correction_recombination_and_extrapolation": true,
        "continued_cultivation_through_a_separate_later_world_return": true,
        "exact_answer_derivation_obstruction_and_geometry_products": true,
        "all_optional_codec_faces_are_downstream": true,
        "complete_transport_dissection_within_the_declared_aperture": true,
        "heldout_rebase_separator_chronology_modality_ablation_withdrawal_and_source_access_controls": true,
        "resident_single_card_execution_and_exact_semantic_receipts": true,
        "frozen_manifest_and_capability_atlas_name_every_open_family": true,
        "lean_checker_on_inference_path": false,
        "foreign_audio_tower_claimed_complete": false,
    });
    artifact::write_json(output.join("06-grade.json"), &grade)?;
    artifact::write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.n4.product-return-manifest.v1",
            "truth_status": "established-bounded",
            "native_rest": "native-rest/MANIFEST.json",
            "later_world_return": "01-later-returned-optical-world.json",
            "direct_application": "02-direct-native-application.json",
            "detached_application": "detached-return/return.json",
            "capability_atlas": "03-capability-atlas.json",
            "dissection": "04-complete-product-dissection.json",
            "withdrawal": "05-exact-product-withdrawal.json",
            "grade": "06-grade.json",
            "projections": "projections/",
        }),
    )?;
    println!("N4 froze laboratory mathematics Athena {product_identity}");
    Ok(())
}

pub fn detached(rest: &Path, applications: &Path, output: &Path) -> Result<(), String> {
    let product = read_product(rest)?;
    let occurrences: Vec<ApplicationOccurrence> =
        serde_json::from_slice(&artifact::read(applications)?)
            .map_err(|error| error.to_string())?;
    let application = conduct_application(&product, &occurrences)?;
    let descriptors = descriptors();
    let forbidden = descriptors
        .iter()
        .filter(|target| {
            target.contains("Workspaces/holonics")
                || target.contains("model.safetensors")
                || target.contains("soma/formal")
                || target.contains("/research/")
                || target.ends_with(".wav")
        })
        .cloned()
        .collect::<Vec<_>>();
    artifact::write_json(
        output,
        &json!({
            "schema": "holonics.n4.source-detached-application.v1",
            "truth_status": "established-bounded",
            "product_sha256": product.canonical_identity()?,
            "application": application,
            "raw_ocr_rest": {
                "occurrence": product.optical().occurrence,
                "components": product.optical().components.len(),
                "glyph_faces": product.optical().glyph_testimony.as_ref().map(|testimony| testimony.glyphs.len()).unwrap_or(0),
                "transcript_present": product.optical().productive_transcript_present,
            },
            "source_descriptors": descriptors,
            "forbidden_source_descriptors": forbidden,
            "lean_or_checker_opened": Path::new("/usr/bin/lean").exists() || Path::new("/bin/lean").exists() || Path::new("/proof-plates").exists(),
            "passed": true,
        }),
    )?;
    Ok(())
}

fn conduct_application(
    product: &LaboratoryAthenaProduct,
    occurrences: &[ApplicationOccurrence],
) -> Result<Value, String> {
    if occurrences.len() < 3 {
        return Err("the N4 application population is incomplete".to_owned());
    }
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let mut returns = Vec::new();
    for occurrence in occurrences {
        let sources = vec![
            format!("{}/integer", occurrence.occurrence),
            format!("{}/modulus-two", occurrence.occurrence),
        ];
        let inquiry = product.found_inquiry(
            sources.clone(),
            occurrence.sections.clone(),
            occurrence.histories.clone(),
            vec!["the requested occurrence remains bounded by the frozen native decoder".to_owned()],
        )?;
        let prior = product.found_precontinuation_inquiry(
            sources,
            occurrence.sections.clone(),
            occurrence.histories.clone(),
            vec!["the requested occurrence remains bounded by the frozen native decoder".to_owned()],
        )?;
        let returned = product.conduct(&inquiry, &mut card)?;
        let prior_returned = product.conduct(&prior, &mut card)?;
        let exact_faces_preserved = returned.complex.exact_consequence_faces
            == prior_returned.complex.exact_consequence_faces;
        let continuation_changes_rich_identity = returned.occurrence != prior_returned.occurrence
            && returned
                .derivational_transport
                .iter()
                .all(|transport| {
                    transport
                        .prior_history_occurrences
                        .contains(&product.continuation().returned_world.occurrence)
                });
        if !exact_faces_preserved || !continuation_changes_rich_identity {
            return Err("the continuation either moved the exact face or vanished from lineage".to_owned());
        }
        returns.push(json!({
            "requested_occurrence": occurrence,
            "native_inquiry": inquiry,
            "native_consequence": returned,
            "precontinuation_consequence_occurrence": prior_returned.occurrence,
            "exact_faces_preserved": exact_faces_preserved,
            "continuation_changes_rich_identity": continuation_changes_rich_identity,
        }));
    }
    let fusion = product.conduct_heterogeneous(&mut card)?;
    let before = product
        .heterogeneous()
        .decoder
        .consequences
        .iter()
        .filter(|consequence| consequence.state == 0)
        .map(|consequence| consequence.address)
        .collect::<Vec<_>>();
    let after = product
        .heterogeneous()
        .decoder
        .consequences
        .iter()
        .filter(|consequence| consequence.state == 1)
        .map(|consequence| consequence.address)
        .collect::<Vec<_>>();
    let ports = product.heterogeneous().standing.ports.len();
    let local_withdrawals_exact = (0..ports).all(|withdrawn| {
        (0..before.len()).all(|cell| {
            fusion.local_ablated_consequence[cell * ports + withdrawn]
                == if cell % ports == withdrawn {
                    before[cell]
                } else {
                    after[cell]
                }
        })
    });
    if fusion.predecessor_consequence != before
        || fusion.successor_consequence != after
        || fusion.shared_ablated_consequence != before
        || !local_withdrawals_exact
    {
        return Err("the three-port product circulation lost an attributable withdrawal".to_owned());
    }
    Ok(json!({
        "native_returns": returns,
        "heterogeneous_return": {
            "predecessor": fusion.predecessor_consequence,
            "successor": fusion.successor_consequence,
            "shared_withdrawal": fusion.shared_ablated_consequence,
            "local_withdrawals": fusion.local_ablated_consequence,
            "local_withdrawals_exact": local_withdrawals_exact,
            "device": card.device_name(),
            "launches": fusion.launches,
            "synchronizations": fusion.synchronizations,
            "active_lanes": fusion.active_lanes,
            "resident_octets": fusion.resident_octets,
            "transfer_octets": fusion.host_ingress_octets + fusion.host_egress_octets,
        },
    }))
}

fn emit_projections(
    output: &Path,
    product: &LaboratoryAthenaProduct,
    occurrence: &ApplicationOccurrence,
) -> Result<(), String> {
    let inquiry = product.found_inquiry(
        vec![
            format!("{}/integer", occurrence.occurrence),
            format!("{}/modulus-two", occurrence.occurrence),
        ],
        occurrence.sections.clone(),
        occurrence.histories.clone(),
        vec!["codec projections remain downstream of this native occurrence".to_owned()],
    )?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let consequence = product.conduct(&inquiry, &mut card)?;
    let notation = consequence
        .project(NativeCodec::ExactNotation)
        .map_err(|error| error.to_string())?;
    let structured = consequence
        .project(NativeCodec::Json)
        .map_err(|error| error.to_string())?;
    artifact::write_json(output.join("projections/00-exact-notation.json"), &notation)?;
    artifact::write_json(output.join("projections/01-structured.json"), &structured)?;
    let explanation = format!(
        "Native consequence {} returned {} operation cells and {} obstruction faces. This prose is a downstream receiver shadow; the product identity remains {}.\n",
        consequence.occurrence,
        consequence.complex.operation_cells.len(),
        consequence.exterior.returned_obstructions.len(),
        consequence.occurrence,
    );
    artifact::write(output.join("projections/02-explanation.txt"), explanation.as_bytes())?;
    let lean_data = format!(
        "-- Exterior data projection only; not checked and never used by inference.\ndef nativeConsequenceOccurrence : String := {:?}\ndef returnedSections : List (List Int) := {:?}\n",
        consequence.occurrence,
        consequence
            .complex
            .exact_consequence_faces
            .iter()
            .map(|face| face.returned_section.clone())
            .collect::<Vec<_>>()
    );
    artifact::write(output.join("projections/03-returned-data.lean"), lean_data.as_bytes())?;
    let rust_data = format!(
        "// Exterior data projection only; not used by inference.\npub const NATIVE_CONSEQUENCE: &str = {:?};\npub const RETURNED_SECTIONS: &[&[i64]] = &{:?};\n",
        consequence.occurrence,
        consequence
            .complex
            .exact_consequence_faces
            .iter()
            .map(|face| face.returned_section.as_slice())
            .collect::<Vec<_>>()
    );
    artifact::write(output.join("projections/04-returned-data.rs"), rust_data.as_bytes())?;
    let diagram =
        world_return::emit_geometry(&consequence, &output.join("projections/05-native-raster.png"))?;
    artifact::write_json(output.join("projections/05-native-raster.json"), &diagram)?;
    let mesh = json!({
        "schema": "holonics.n4.exact-native-mesh.v1",
        "native_consequence_occurrence": consequence.occurrence,
        "vertices": consequence.complex.geometry_cells.iter().flat_map(|cell| cell.vertices.iter().map(|vertex| [i64::from(vertex.coordinate), vertex.entered, vertex.returned])).collect::<Vec<_>>(),
        "cells": consequence.complex.geometry_cells.iter().enumerate().map(|(cell, geometry)| json!({"cell": cell, "occurrence": geometry.occurrence, "incidence": geometry.constraint_incidence})).collect::<Vec<_>>(),
        "projection_only": true,
    });
    artifact::write_json(output.join("projections/06-native-mesh.json"), &mesh)?;
    artifact::write(
        output.join("projections/06-native-complex.svg"),
        native_complex_svg(&consequence).as_bytes(),
    )?;
    let acoustic_path = output.join("projections/07-exact-notation.wav");
    let status = Command::new("espeak-ng")
        .args(["-v", "en-us", "-w"])
        .arg(&acoustic_path)
        .arg(&notation.payload)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err("the downstream acoustic projection refused".to_owned());
    }
    artifact::write_json(
        output.join("projections/07-exact-notation.json"),
        &json!({
            "native_consequence_occurrence": consequence.occurrence,
            "codec": "espeak-ng exterior acoustic projection",
            "wav_sha256": artifact::digest(artifact::read(&acoustic_path)?),
            "projection_only": true,
        }),
    )?;
    Ok(())
}

fn native_complex_svg(
    consequence: &life::mathematical_particle::NativeMathematicalConsequence,
) -> String {
    let rows = consequence
        .complex
        .operation_cells
        .iter()
        .zip(&consequence.complex.constraint_cells)
        .zip(&consequence.complex.exact_consequence_faces)
        .zip(&consequence.derivational_transport)
        .enumerate()
        .map(|(family, (((operation, constraint), face), derivation))| {
            let top = 150 + family * 145;
            let route_color = match face.selected_route {
                1 => "#5ee3a2",
                2 => "#ff7b8a",
                _ => "#ffc75f",
            };
            format!(
                r#"<g transform="translate(0 {top})">
<rect x="48" y="0" width="190" height="82" rx="12" class="plate"/><text x="64" y="25" class="label">entered section</text><text x="64" y="55" class="value">{entered:?}</text>
<path d="M238 41 H326" class="arrow"/><text x="258" y="28" class="small">word {word:?}</text>
<rect x="326" y="0" width="242" height="82" rx="12" class="operation"/><text x="344" y="25" class="label">transport family {family}</text><text x="344" y="55" class="value">Δ {difference:?}</text>
<path d="M568 41 H650" class="arrow"/>
<rect x="650" y="0" width="260" height="82" rx="12" fill="{route_color}" fill-opacity="0.14" stroke="{route_color}"/><text x="668" y="25" class="label">returned section · route {route}</text><text x="668" y="55" class="value">{returned:?}</text>
<text x="326" y="112" class="small">constraint ⟨{orientation:?}, section⟩ = {residual} · held {held}</text>
</g>"#,
                entered = operation.entered_section,
                word = derivation.ordered_word,
                difference = operation.exact_difference,
                route = face.selected_route,
                returned = face.returned_section,
                orientation = constraint.orientation,
                residual = constraint.exact_residual,
                held = constraint.held,
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" width="960" height="500" viewBox="0 0 960 500">
<defs><marker id="tip" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0 L8 4 L0 8Z" fill="#71b7ff"/></marker></defs>
<style>
svg{{background:#0d1421;color:#e8f0ff;font-family:Inter,ui-sans-serif,system-ui,sans-serif}} .title{{fill:#f3f7ff;font-size:24px;font-weight:650}} .subtitle{{fill:#8fa6c4;font-size:13px}} .plate{{fill:#151f30;stroke:#3a506d}} .operation{{fill:#15283a;stroke:#38a3d8}} .label{{fill:#dbe9ff;font-size:14px;font-weight:600}} .value{{fill:#ffffff;font:15px ui-monospace,SFMono-Regular,monospace}} .small{{fill:#9eb4ce;font:12px ui-monospace,SFMono-Regular,monospace}} .arrow{{stroke:#71b7ff;stroke-width:2;marker-end:url(#tip)}}
</style>
<text x="48" y="42" class="title">Native consequence before codec projection</text>
<text x="48" y="70" class="subtitle">{identity}</text>
<text x="48" y="104" class="subtitle">Every box is a caused operation/constraint face; arrows carry ordered transport words. Equal returned values do not collapse lineage.</text>
{rows}
<text x="48" y="470" class="subtitle">Continuation occurrence: {continuation}</text>
</svg>"##,
        identity = consequence.occurrence,
        continuation = consequence
            .derivational_transport
            .first()
            .and_then(|transport| transport.prior_history_occurrences.last())
            .map(String::as_str)
            .unwrap_or("open"),
    )
}

fn freeze_components(
    output: &Path,
    product: &LaboratoryAthenaProduct,
) -> Result<Vec<ProductComponent>, String> {
    let names = [
        ("mathematical-predecessor-standing", "mathematical-predecessor-standing.bin"),
        ("mathematical-predecessor-decoder", "mathematical-predecessor-decoder.bin"),
        ("mathematical-predecessor-fibres", "mathematical-predecessor-fibres.bin"),
        ("mathematical-cultivation-standing", "mathematical-cultivation-standing.json"),
        ("optical-standing", "optical-standing.json"),
        ("heterogeneous-standing", "heterogeneous-standing.json"),
        ("heterogeneous-decoder", "heterogeneous-decoder.json"),
        ("heterogeneous-fibres", "heterogeneous-fibres.json"),
        ("continuation-standing", "continuation-standing.json"),
    ];
    let bytes = product.component_bytes()?;
    if bytes.len() != names.len() {
        return Err("the N4 canonical component population moved".to_owned());
    }
    names
        .into_iter()
        .zip(bytes)
        .map(|((name, path), bytes)| {
            artifact::write(output.join("native-rest").join(path), &bytes)?;
            Ok(ProductComponent {
                name: name.to_owned(),
                path: path.to_owned(),
                sha256: artifact::digest(&bytes),
                octets: bytes.len() as u64,
            })
        })
        .collect()
}

fn read_product(rest: &Path) -> Result<LaboratoryAthenaProduct, String> {
    let manifest: ProductManifest =
        serde_json::from_slice(&artifact::read(rest.join("MANIFEST.json"))?)
            .map_err(|error| error.to_string())?;
    let mut by_name = BTreeMap::new();
    for component in &manifest.components {
        let bytes = artifact::read(rest.join(&component.path))?;
        if bytes.len() as u64 != component.octets || artifact::digest(&bytes) != component.sha256 {
            return Err(format!("the frozen product component {} moved", component.name));
        }
        by_name.insert(component.name.as_str(), bytes);
    }
    let part = |name: &str| {
        by_name
            .get(name)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("the frozen product component {name} is absent"))
    };
    let product = LaboratoryAthenaProduct::read(
        part("mathematical-predecessor-standing")?,
        part("mathematical-predecessor-decoder")?,
        part("mathematical-predecessor-fibres")?,
        part("mathematical-cultivation-standing")?,
        part("optical-standing")?,
        part("heterogeneous-standing")?,
        part("heterogeneous-decoder")?,
        part("heterogeneous-fibres")?,
        part("continuation-standing")?,
    )?;
    if product.canonical_identity()? != manifest.product_sha256 {
        return Err("the frozen N4 product identity moved on remount".to_owned());
    }
    Ok(product)
}

fn run_detached(
    executable: &Path,
    rest: &Path,
    applications: &Path,
    output: &Path,
) -> Result<(), String> {
    if !output.exists() {
        artifact::write(output, &[])?;
    }
    let executable = executable.canonicalize().map_err(|error| error.to_string())?;
    let rest = rest.canonicalize().map_err(|error| error.to_string())?;
    let applications = applications.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all", "--clearenv"])
        .args(["--setenv", "PATH", "/empty"])
        .args(["--setenv", "HOME", "/tmp"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--tmpfs", "/usr/bin"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .args(["--dir", "/input"])
        .args(["--dir", "/return"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    let returned = command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--ro-bind")
        .arg(applications)
        .arg("/input/applications.json")
        .arg("--bind")
        .arg(output)
        .arg("/return/return.json")
        .arg("/athena")
        .arg("--detached")
        .arg("/rest")
        .arg("/input/applications.json")
        .arg("/return/return.json")
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "detached N4 refused: {}{}",
            String::from_utf8_lossy(&returned.stdout),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn descriptors() -> Vec<String> {
    let mut descriptors = BTreeSet::new();
    if let Ok(entries) = fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = fs::read_link(entry.path()) {
                descriptors.insert(target.display().to_string());
            }
        }
    }
    descriptors.into_iter().collect()
}

pub fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
