//! L3 — prose, notation, raw optical geometry, Rust, Lean, and laboratory dialogue cross one
//! material-to-native factorization without letting their exterior faces route Athena.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    image::{ExactRaster, ExactRgb, ImageExtent},
};
use life::{
    mathematical_source::{recover_optical_passage, OpticalPassage},
    native_intelligence::{
        compare_material_factorizations, AddressedMaterialOccurrence, CausalOperationWorldReturn,
        CausalResultCell, ExteriorWorldReturnTestimony, MaterialFactorizationAperture,
        MaterialFactorizationReturn, MaterialNativeFactorization, SituatedCultivatedEcologyRest,
    },
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const L2_REST: &str = "output/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2/athena-situated-cultivated.rest";
const DEFAULT_OUT: &str = "output/the_material_faces_rebase_into_one_situated_athena_aperture_l3";

#[derive(Serialize)]
struct MaterialReceipt<'a> {
    material: &'a AddressedMaterialOccurrence,
    factorization: &'a MaterialNativeFactorization,
}

#[derive(Serialize)]
struct OpticalReceipt<'a> {
    primary: &'a OpticalPassage,
    rerendered: &'a OpticalPassage,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let out = root.join(DEFAULT_OUT);
    if out.exists() {
        return Err(format!(
            "L3 output already exists; preserve or explicitly remove {} before another occurrence",
            out.display()
        ));
    }

    let l2_bytes = fs::read(root.join(L2_REST)).map_err(|error| error.to_string())?;
    let l2 = SituatedCultivatedEcologyRest::read(&l2_bytes).map_err(|error| error.to_string())?;
    let l2_identity = l2.identity().to_owned();
    let aperture = MaterialFactorizationAperture::found(&l2).map_err(|error| error.to_string())?;

    let prose = material(
        "l3/material/prose/two-plus-two",
        b"two plus two",
        &["ordinary-English", "operator-voice"],
    )?;
    let prose_revoiced = material(
        "l3/material/prose/revoiced",
        b"combine a pair with another pair as one disjoint population",
        &["ordinary-English", "passive-revoice"],
    )?;
    let notation = material(
        "l3/material/notation/addition",
        b"2 + 2",
        &["exact-notation", "utf8"],
    )?;
    let dialogue = material(
        "l3/material/dialogue/addition",
        b"Brandon: let the two disjoint pairs return as one caused population.",
        &["laboratory-dialogue", "named-speaker"],
    )?;
    let multiplication = material(
        "l3/material/notation/multiplication",
        b"2 * 2",
        &["exact-notation", "utf8"],
    )?;

    let prose_return = union_return(&prose, "prose", operator_testimony("prose", b"4")?)?;
    let prose_revoiced_return = union_return(
        &prose_revoiced,
        "prose-revoiced",
        operator_testimony("prose-revoiced", b"4")?,
    )?;
    let notation_return =
        union_return(&notation, "notation", operator_testimony("notation", b"4")?)?;
    let dialogue_return =
        union_return(&dialogue, "dialogue", operator_testimony("dialogue", b"4")?)?;
    let multiplication_return = product_return(
        &multiplication,
        "multiplication",
        operator_testimony("multiplication", b"4")?,
    )?;

    let prose_factor = aperture
        .factor(&prose, &prose_return)
        .map_err(|error| error.to_string())?;
    let prose_revoiced_factor = aperture
        .factor(&prose_revoiced, &prose_revoiced_return)
        .map_err(|error| error.to_string())?;
    let notation_factor = aperture
        .factor(&notation, &notation_return)
        .map_err(|error| error.to_string())?;
    let dialogue_factor = aperture
        .factor(&dialogue, &dialogue_return)
        .map_err(|error| error.to_string())?;
    let multiplication_factor = aperture
        .factor(&multiplication, &multiplication_return)
        .map_err(|error| error.to_string())?;

    // Real exterior code and kernel returns. Their verdicts remain lineage; the returned causal
    // incidence, rather than a filename or language name, supplies the operation section.
    let rust_source = root.join("research/fixtures/l3_cross_codec/addition.rs");
    let rust_renamed_source = root.join("research/fixtures/l3_cross_codec/addition_renamed.rs");
    let (rust_payload, rust_testimony) = rust_world_return(&rust_source, "rust")?;
    let (rust_renamed_payload, rust_renamed_testimony) =
        rust_world_return(&rust_renamed_source, "rust-renamed")?;
    let rust = material(
        "l3/material/rust/addition",
        &rust_payload,
        &["Rust", "compiled-source"],
    )?;
    let rust_renamed = material(
        "l3/material/rust/addition-renamed",
        &rust_renamed_payload,
        &["Rust", "compiled-source", "renamed-bindings"],
    )?;
    let rust_return = union_return(&rust, "rust", rust_testimony)?;
    let rust_renamed_return = union_return(&rust_renamed, "rust-renamed", rust_renamed_testimony)?;
    let rust_factor = aperture
        .factor(&rust, &rust_return)
        .map_err(|error| error.to_string())?;
    let rust_renamed_factor = aperture
        .factor(&rust_renamed, &rust_renamed_return)
        .map_err(|error| error.to_string())?;

    let lean_source = root.join("research/fixtures/l3_cross_codec/Addition.lean");
    let (lean_payload, lean_testimony) = lean_world_return(&root, &lean_source)?;
    let lean = material(
        "l3/material/lean/addition",
        &lean_payload,
        &["Lean", "kernel-checked-source"],
    )?;
    let lean_return = union_return(&lean, "lean", lean_testimony)?;
    let lean_factor = aperture
        .factor(&lean, &lean_return)
        .map_err(|error| error.to_string())?;

    // Two raw raster occurrences found their component populations without OCR. Translation and
    // reflow alter every optical address but preserve the declared disjoint-population square.
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let optical_primary = optical_passage(&mut card, "primary", 0)?;
    let optical_rerendered = optical_passage(&mut card, "rerendered", 1)?;
    let optical_material = material(
        "l3/material/optical/primary",
        &optical_primary.0,
        &["raw-raster", "no-transcript", "no-ocr"],
    )?;
    let optical_rerendered_material = material(
        "l3/material/optical/rerendered",
        &optical_rerendered.0,
        &["raw-raster", "translated-reflow", "no-ocr"],
    )?;
    let optical_return = optical_union_return(
        &optical_material,
        "optical-primary",
        &optical_primary.1,
        operator_testimony("optical-primary", &optical_primary.0)?,
    )?;
    let optical_rerendered_return = optical_union_return(
        &optical_rerendered_material,
        "optical-rerendered",
        &optical_rerendered.1,
        operator_testimony("optical-rerendered", &optical_rerendered.0)?,
    )?;
    let optical_factor = aperture
        .factor(&optical_material, &optical_return)
        .map_err(|error| error.to_string())?;
    let optical_rerendered_factor = aperture
        .factor(&optical_rerendered_material, &optical_rerendered_return)
        .map_err(|error| error.to_string())?;

    // The same optical component population also admits a product reading when no grouping
    // receiver has returned. Both complete candidates survive; no glyph string is guessed.
    let optical_product_return = product_return_from_inputs(
        &optical_material,
        "optical-product-candidate",
        optical_return.left_input.clone(),
        optical_return.right_input.clone(),
        operator_testimony("optical-product-candidate", &optical_primary.0)?,
    )?;
    let ambiguous = aperture
        .factor_candidates(
            &optical_material,
            &[optical_return.clone(), optical_product_return],
        )
        .map_err(|error| error.to_string())?;
    let MaterialFactorizationReturn::Insufficient(ambiguity) = ambiguous else {
        return Err("the unresolved optical population was guessed closed".to_owned());
    };

    let prose_notation = compare_material_factorizations(
        &prose_factor,
        &notation_factor,
        "complete-operation-and-successor-history",
    );
    let prose_revoice = compare_material_factorizations(
        &prose_factor,
        &prose_revoiced_factor,
        "complete-operation-and-successor-history",
    );
    let notation_rust = compare_material_factorizations(
        &notation_factor,
        &rust_factor,
        "complete-operation-and-successor-history",
    );
    let rust_rename = compare_material_factorizations(
        &rust_factor,
        &rust_renamed_factor,
        "complete-operation-and-successor-history",
    );
    let notation_lean = compare_material_factorizations(
        &notation_factor,
        &lean_factor,
        "complete-operation-and-successor-history",
    );
    let notation_dialogue = compare_material_factorizations(
        &notation_factor,
        &dialogue_factor,
        "complete-operation-and-successor-history",
    );
    let optical_rerender = compare_material_factorizations(
        &optical_factor,
        &optical_rerendered_factor,
        "complete-operation-and-successor-history",
    );
    let equal_value_separator = compare_material_factorizations(
        &notation_factor,
        &multiplication_factor,
        "exact-returned-population-plus-successor-intervention",
    );

    let stripped_factor = aperture
        .factor(&notation.without_delivery_faces(), &notation_return)
        .map_err(|error| error.to_string())?;
    let shuffled_factor = aperture
        .factor(&notation.with_reordered_delivery_faces(), &notation_return)
        .map_err(|error| error.to_string())?;
    let delivery_labels_inert = notation_factor.native_operation_identity_sha256
        == stripped_factor.native_operation_identity_sha256
        && notation_factor.relation_current_section == stripped_factor.relation_current_section
        && notation_factor.factor_support == stripped_factor.factor_support
        && notation_factor.native_operation_identity_sha256
            == shuffled_factor.native_operation_identity_sha256
        && notation_factor.relation_current_section == shuffled_factor.relation_current_section
        && notation_factor.factor_support == shuffled_factor.factor_support;

    let addition_identity = prose_factor.native_operation_identity_sha256.clone();
    let all_addition = [
        &prose_revoiced_factor,
        &notation_factor,
        &dialogue_factor,
        &rust_factor,
        &rust_renamed_factor,
        &lean_factor,
        &optical_factor,
        &optical_rerendered_factor,
    ]
    .iter()
    .all(|factor| factor.native_operation_identity_sha256 == addition_identity);
    let all_naturality = [
        &prose_notation,
        &prose_revoice,
        &notation_rust,
        &rust_rename,
        &notation_lean,
        &notation_dialogue,
        &optical_rerender,
    ]
    .iter()
    .all(|receipt| receipt.square_commutes);
    let separated = !equal_value_separator.square_commutes
        && equal_value_separator
            .shortest_separator
            .as_ref()
            .is_some_and(|separator| {
                [
                    separator.left_returned_population,
                    separator.right_returned_population,
                ] == [5, 6]
            });
    let complete_rank_four_support = prose_factor.factor_support.len() == 4
        && prose_factor.complete_symmetric_family_support.len() == 10;
    let ambiguous_optics_retained = ambiguity.candidate_sections.len() == 2
        && ambiguity.reconstruction_fibre.len() == 2
        && [
            ambiguity.shortest_separator.left_returned_population,
            ambiguity.shortest_separator.right_returned_population,
        ] == [5, 6];
    let passed = all_addition
        && all_naturality
        && separated
        && delivery_labels_inert
        && complete_rank_four_support
        && ambiguous_optics_retained
        && rust_return.apparatus.accepted
        && lean_return.apparatus.accepted
        && !optical_primary.1.productive_transcript_present
        && !optical_primary.1.productive_text_layer_present;
    if !passed {
        return Err("the complete L3 receiver refused".to_owned());
    }

    fs::create_dir_all(&out).map_err(|error| error.to_string())?;
    write_json(
        &out.join("00-standing-reuse-and-owner-receipt.json"),
        &json!({
            "schema": "soma-life.l3.standing-reuse-receipt.v1",
            "truth_status": "established-bounded",
            "one_continuing_body": l2_identity,
            "l2_wire_sha256": hex(&l2_bytes),
            "ingress_port": "addressed material occurrence plus caused incidence world return",
            "hot_owner": "SituatedCultivatedEcologyRest rank-four receiver chart and exact symmetric constitutive body",
            "return_port": "NativeMathematicalComplex plus situated factor support or material receiver insufficiency",
            "requested_artifact": DEFAULT_OUT,
            "new_owner": "one material-native factorization relation",
            "new_parser_or_router": false,
            "second_rest": false,
        }),
    )?;
    write_json(
        &out.join("01-cross-codec-native-factorizations.json"),
        &vec![
            MaterialReceipt {
                material: &prose,
                factorization: &prose_factor,
            },
            MaterialReceipt {
                material: &prose_revoiced,
                factorization: &prose_revoiced_factor,
            },
            MaterialReceipt {
                material: &notation,
                factorization: &notation_factor,
            },
            MaterialReceipt {
                material: &dialogue,
                factorization: &dialogue_factor,
            },
            MaterialReceipt {
                material: &rust,
                factorization: &rust_factor,
            },
            MaterialReceipt {
                material: &rust_renamed,
                factorization: &rust_renamed_factor,
            },
            MaterialReceipt {
                material: &lean,
                factorization: &lean_factor,
            },
            MaterialReceipt {
                material: &optical_material,
                factorization: &optical_factor,
            },
            MaterialReceipt {
                material: &optical_rerendered_material,
                factorization: &optical_rerendered_factor,
            },
        ],
    )?;
    write_json(
        &out.join("02-operation-intervention-separator.json"),
        &json!({
            "truth_status": "implemented-exact",
            "addition": notation_factor,
            "multiplication": multiplication_factor,
            "comparison": equal_value_separator,
            "equal_displayed_population": 4,
            "adjoin_one_member": {"disjoint_union": 5, "independent_product": 6},
        }),
    )?;
    write_json(
        &out.join("03-naturality-and-delivery-controls.json"),
        &json!({
            "truth_status": "implemented-exact",
            "prose_notation": prose_notation,
            "prose_revoice": prose_revoice,
            "notation_rust": notation_rust,
            "rust_variable_rename": rust_rename,
            "notation_lean": notation_lean,
            "notation_dialogue": notation_dialogue,
            "optical_rerender": optical_rerender,
            "delivery_labels_removed_and_reordered_without_native_change": delivery_labels_inert,
        }),
    )?;
    write_json(
        &out.join("04-optical-potential-and-insufficiency.json"),
        &json!({
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "optical": OpticalReceipt { primary: &optical_primary.1, rerendered: &optical_rerendered.1 },
            "ambiguity": ambiguity,
            "ocr_or_transcript_required": false,
        }),
    )?;
    write_json(
        &out.join("05-exterior-code-and-kernel-returns.json"),
        &json!({
            "truth_status": "measured",
            "rust": rust_return.apparatus,
            "rust_renamed": rust_renamed_return.apparatus,
            "lean": lean_return.apparatus,
            "verdict_or_tool_label_routes_native_section": false,
            "lean_inside_athena_inference": false,
        }),
    )?;
    write_json(
        &out.join("06-l3-primary-grade.json"),
        &json!({
            "schema": "soma-life.l3.cross-codec-material-aperture-grade.v1",
            "truth_status": "established-bounded-implemented-exact-measured",
            "passed": passed,
            "same_complete_addition_consequence": all_addition,
            "declared_naturality_squares_commute": all_naturality,
            "equal_value_operations_separate_under_successor_intervention": separated,
            "delivery_labels_do_not_route": delivery_labels_inert,
            "rank_four_support_and_ten_symmetric_families": complete_rank_four_support,
            "ambiguous_optics_return_complete_fibre": ambiguous_optics_retained,
            "native_mathematical_complex_precedes_surface_projection": true,
            "material_family": ["ordinary prose", "notation", "raw optical geometry", "Rust", "Lean", "laboratory dialogue"],
            "forbidden": {
                "parser_authored_topology": false,
                "language_specific_router": false,
                "ocr_string_collapse": false,
                "checker_inside_hot_inference": false,
                "material_kind_as_native_state": false,
                "equal_answer_as_operation_equality": false,
            },
            "open_exterior": [
                "unrestricted surface recovery beyond caused disjoint-union/product returns",
                "perspective-sensitive outward prose is L4",
                "laboratory world-tube cultivation is L5",
            ],
        }),
    )?;

    println!(
        "L3 passed: nine addition faces share {}, 2+2 / 2*2 separate as 5 / 6, raw optics retained two candidates, and all four situated directions with ten symmetric families returned",
        addition_identity
    );
    Ok(())
}

fn material(
    occurrence: &str,
    payload: &[u8],
    delivery_faces: &[&str],
) -> Result<AddressedMaterialOccurrence, String> {
    AddressedMaterialOccurrence::found(
        occurrence,
        payload,
        None,
        delivery_faces
            .iter()
            .map(|face| (*face).to_owned())
            .collect(),
        vec![
            "material interpretation outside the returned causal population remains open"
                .to_owned(),
        ],
    )
    .map_err(|error| error.to_string())
}

fn operator_testimony(name: &str, payload: &[u8]) -> Result<ExteriorWorldReturnTestimony, String> {
    ExteriorWorldReturnTestimony::found(
        format!("l3/world/{name}"),
        "caused-finite-population-return",
        true,
        payload,
        vec!["the apparatus face is lineage and does not route native support".to_owned()],
    )
    .map_err(|error| error.to_string())
}

fn union_return(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    apparatus: ExteriorWorldReturnTestimony,
) -> Result<CausalOperationWorldReturn, String> {
    let left = (0..2)
        .map(|at| format!("l3/{prefix}/left/{at}"))
        .collect::<Vec<_>>();
    let right = (0..2)
        .map(|at| format!("l3/{prefix}/right/{at}"))
        .collect::<Vec<_>>();
    union_return_from_inputs(material, prefix, left, right, apparatus)
}

fn union_return_from_inputs(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    left: Vec<String>,
    right: Vec<String>,
    apparatus: ExteriorWorldReturnTestimony,
) -> Result<CausalOperationWorldReturn, String> {
    let result = left
        .iter()
        .enumerate()
        .map(|(at, member)| CausalResultCell {
            occurrence: format!("l3/{prefix}/returned/left/{at}"),
            left_member: Some(member.clone()),
            right_member: None,
        })
        .chain(
            right
                .iter()
                .enumerate()
                .map(|(at, member)| CausalResultCell {
                    occurrence: format!("l3/{prefix}/returned/right/{at}"),
                    left_member: None,
                    right_member: Some(member.clone()),
                }),
        )
        .collect();
    CausalOperationWorldReturn::found(
        format!("l3/{prefix}/operation-return"),
        material.occurrence.clone(),
        left,
        right,
        result,
        apparatus,
        vec![
            "successor histories beyond the declared one-member intervention remain open"
                .to_owned(),
        ],
    )
    .map_err(|error| error.to_string())
}

fn product_return(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    apparatus: ExteriorWorldReturnTestimony,
) -> Result<CausalOperationWorldReturn, String> {
    let left = (0..2)
        .map(|at| format!("l3/{prefix}/left/{at}"))
        .collect::<Vec<_>>();
    let right = (0..2)
        .map(|at| format!("l3/{prefix}/right/{at}"))
        .collect::<Vec<_>>();
    product_return_from_inputs(material, prefix, left, right, apparatus)
}

fn product_return_from_inputs(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    left: Vec<String>,
    right: Vec<String>,
    apparatus: ExteriorWorldReturnTestimony,
) -> Result<CausalOperationWorldReturn, String> {
    let result = left
        .iter()
        .enumerate()
        .flat_map(|(left_at, left_member)| {
            right
                .iter()
                .enumerate()
                .map(move |(right_at, right_member)| CausalResultCell {
                    occurrence: format!("l3/{prefix}/returned/{left_at}/{right_at}"),
                    left_member: Some(left_member.clone()),
                    right_member: Some(right_member.clone()),
                })
        })
        .collect();
    CausalOperationWorldReturn::found(
        format!("l3/{prefix}/operation-return"),
        material.occurrence.clone(),
        left,
        right,
        result,
        apparatus,
        vec![
            "successor histories beyond the declared one-member intervention remain open"
                .to_owned(),
        ],
    )
    .map_err(|error| error.to_string())
}

fn rust_world_return(
    source: &Path,
    name: &str,
) -> Result<(Vec<u8>, ExteriorWorldReturnTestimony), String> {
    let source_bytes = fs::read(source).map_err(|error| error.to_string())?;
    let binary = env::temp_dir().join(format!(
        "holonics-l3-{}-{}",
        std::process::id(),
        hex(&source_bytes)
    ));
    let compiled = Command::new("rustc")
        .arg("--edition=2021")
        .arg(source)
        .arg("-o")
        .arg(&binary)
        .output()
        .map_err(|error| error.to_string())?;
    if !compiled.status.success() {
        return Err(format!(
            "Rust exterior compilation refused: {}",
            String::from_utf8_lossy(&compiled.stderr)
        ));
    }
    let executed = Command::new(&binary)
        .output()
        .map_err(|error| error.to_string())?;
    let _ = fs::remove_file(&binary);
    if !executed.status.success() || executed.stdout != b"4\n" {
        return Err("Rust exterior world returned another population".to_owned());
    }
    let mut returned = format!(
        "compile-status={}\nrun-status={}\n",
        compiled.status, executed.status
    )
    .into_bytes();
    returned.extend_from_slice(&executed.stdout);
    let testimony = ExteriorWorldReturnTestimony::found(
        format!("l3/world/{name}"),
        "rustc-and-executed-world",
        true,
        &returned,
        vec![
            "compiler and executable are exterior apparatus, absent from Athena's hot closure"
                .to_owned(),
        ],
    )
    .map_err(|error| error.to_string())?;
    Ok((source_bytes, testimony))
}

fn lean_world_return(
    root: &Path,
    source: &Path,
) -> Result<(Vec<u8>, ExteriorWorldReturnTestimony), String> {
    let source_bytes = fs::read(source).map_err(|error| error.to_string())?;
    let returned = Command::new("lake")
        .arg("env")
        .arg("lean")
        .arg(source)
        .current_dir(root.join("soma/formal/elementary-holonics"))
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "Lean exterior kernel refused: {}{}",
            String::from_utf8_lossy(&returned.stdout),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    let mut payload = format!("kernel-status={}\n", returned.status).into_bytes();
    payload.extend_from_slice(&returned.stdout);
    payload.extend_from_slice(&returned.stderr);
    let testimony = ExteriorWorldReturnTestimony::found(
        "l3/world/lean",
        "lean-kernel-world",
        true,
        &payload,
        vec!["Lean is exterior theorem testimony and is absent from Athena inference".to_owned()],
    )
    .map_err(|error| error.to_string())?;
    Ok((source_bytes, testimony))
}

fn optical_passage(
    card: &mut CudaRefineExecutor,
    name: &str,
    variant: u32,
) -> Result<(Vec<u8>, OpticalPassage), String> {
    let width = 40u32;
    let height = 20u32;
    let white = ExactRgb {
        red: 255,
        green: 255,
        blue: 255,
    };
    let black = ExactRgb {
        red: 0,
        green: 0,
        blue: 0,
    };
    let mut samples = vec![white; (width * height) as usize];
    let points = if variant == 0 {
        [(4, 7), (9, 7), (25, 7), (30, 7)]
    } else {
        [(5, 6), (11, 9), (27, 6), (33, 9)]
    };
    for (left, top) in points {
        for row in top..top + 2 {
            for column in left..left + 2 {
                samples[(row * width + column) as usize] = black;
            }
        }
    }
    let raster = ExactRaster::new(ImageExtent { width, height }, samples)
        .map_err(|error| error.to_string())?;
    let encoded = raster.ppm_bytes();
    let passage = recover_optical_passage(
        card,
        format!("l3/raw-optical/{name}/{}", hex(&encoded)),
        "content-addressed-exact-raster",
        &encoded,
        &raster,
        white,
    )
    .map_err(|error| error.to_string())?;
    if passage.components.len() != 4
        || passage.productive_transcript_present
        || passage.productive_text_layer_present
    {
        return Err(format!(
            "the raw optical control returned {} components or imported text",
            passage.components.len()
        ));
    }
    Ok((encoded, passage))
}

fn optical_union_return(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    passage: &OpticalPassage,
    apparatus: ExteriorWorldReturnTestimony,
) -> Result<CausalOperationWorldReturn, String> {
    let mut components = passage.components.iter().collect::<Vec<_>>();
    components.sort_by_key(|component| component.bounds.left + component.bounds.right);
    let gaps = components
        .windows(2)
        .enumerate()
        .map(|(at, pair)| (pair[1].bounds.left - pair[0].bounds.right, at + 1))
        .collect::<Vec<_>>();
    let split = gaps
        .iter()
        .max_by_key(|(gap, _)| *gap)
        .map(|(_, split)| *split)
        .ok_or("the optical component population has no separating gap")?;
    if split != 2 {
        return Err("the declared optical grouping receiver did not return two pairs".to_owned());
    }
    let left = components[..split]
        .iter()
        .map(|component| component.address.clone())
        .collect();
    let right = components[split..]
        .iter()
        .map(|component| component.address.clone())
        .collect();
    union_return_from_inputs(material, prefix, left, right, apparatus)
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn workspace_root() -> Result<PathBuf, String> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| error.to_string())
}

fn hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
