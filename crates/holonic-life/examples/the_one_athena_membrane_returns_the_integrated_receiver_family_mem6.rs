//! MEM6 release receiver over one source-detached, returned Athena body.
//!
//! The driver supplies exterior occurrences and inspects public returns. It contains no deed
//! mode, response template, lexical association, semantic route, or candidate sentence.

use std::{
    any::Any,
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use holonic_engine::{
    quantity::{BaseUnits, Dimension},
    receiver_exact_compression::ReceiverId,
    BoundaryId, ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    mathematical_source::{ExactAcousticOccurrence, HierarchicalOpticalPassage},
    native_intelligence::{
        compare_material_factorizations, realize_material_source, AddressedMaterialOccurrence,
        AdmittedReturnedAffineLaboratoryRestWitness, CausalOperationWorldReturn, CausalResultCell,
        ExactMembraneChartPassage, ExteriorActionCurrent, ExteriorOccurrenceTransducer,
        ExteriorRadiationSurface, ExteriorWorldReturnTestimony,
        HierarchicalOpticalMaterialCandidates, HierarchicalOpticalMaterialReturn,
        MaterialFactorizationAperture, MaterialFactorizationReturn, MaterialSourceCodec,
        MembraneConsequence, MembraneCrossingReceipt, MembraneStanding, NativeCausalMembrane,
        NativeRadiationAperture, NativeRadiationSection, ReturnedAffineLaboratoryRest,
    },
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    ".local/artifacts/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
    "athena-returned-membrane-cultivated.rest"
);
const REST_WIRE_SHA256: &str = "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad";
const REST_IDENTITY_SHA256: &str =
    "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded";
const VALIDATION_RECEIPT_SHA256: &str =
    "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178";
const OPTICAL: &str =
    ".local/artifacts/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const OPTICAL_RAW: &str =
    ".local/artifacts/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const ACOUSTIC: &str = concat!(
    ".local/artifacts/the_laboratory_mathematics_athena_unifies_native_inference_ocr_and_three_port_transport/",
    "projections/07-exact-notation.wav"
);
const OUTPUT: &str = ".local/artifacts/the_one_athena_membrane_returns_the_integrated_receiver_family_mem6";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Mem6Grade {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    rested_identity_sha256: String,
    participant_and_refinement_surfaces: Vec<ExteriorRadiationSurface>,
    refinement_recurrence: Vec<ReturnedRefinementReceipt>,
    material_naturality: Value,
    operation_separator: Value,
    optical_return: Value,
    acoustic_return: Value,
    code_return: Value,
    common_membrane_crossings: Vec<MembraneCrossingReceipt>,
    shared_contact: holonic_engine::cuda_refine::ResidentMembraneInteriorReturn,
    disjoint_contact: holonic_engine::cuda_refine::ResidentMembraneInteriorReturn,
    participant_surfaces_distinct_and_receiver_faithful: bool,
    refinement_surfaces_distinct_and_receiver_faithful: bool,
    refinements_are_caused_by_the_returned_participant_surface: bool,
    mathematics_operation_natural_across_codecs: bool,
    equal_value_operations_separated_by_successor: bool,
    optical_potential_fibre_retained: bool,
    acoustic_exact_source_fibre_returned: bool,
    code_compiled_and_transition_atlas_returned: bool,
    every_exterior_family_crossed_one_mouth: bool,
    shared_contact_nonzero_and_disjoint_control_zero: bool,
    targeted_ablation_changed_response: bool,
    unrelated_ablation_preserved_response: bool,
    exact_restoration_and_source_detached_remount: bool,
    internal_deed_or_semantic_mode_present: bool,
    lean_in_runtime: bool,
    expected_answer_or_surface_consulted: bool,
    open_exterior: Vec<String>,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct ReturnedRefinementReceipt {
    prior_radiation_identity_sha256: String,
    prior_surface_sha256: String,
    refinement_occurrence: String,
    refinement_source_sha256: String,
    same_rested_identity_sha256: String,
    returned_surface_was_mounted_as_exterior_material: bool,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    let wire = fs::read(root.join(REST)).map_err(display)?;
    let witness = admitted_witness()?;
    let rest = ReturnedAffineLaboratoryRest::read_admitted(&wire, &witness).map_err(display)?;
    let rested_identity_sha256 = rest.identity().to_owned();

    // Operation identity is returned from caused populations. Delivery spellings remain controls.
    let prose_material = material(
        "mem6/material/prose/addition",
        b"two plus two",
        "ordinary-prose",
    )?;
    let notation_material = material(
        "mem6/material/notation/addition",
        b"2 + 2",
        "mathematical-notation",
    )?;
    let rust_material = material(
        "mem6/material/rust/addition",
        b"left.into_iter().chain(right).count()",
        "rust-source",
    )?;
    let prose_world = population_return(&prose_material, "mem6/prose-addition", false, 2, 2)?;
    let notation_world =
        population_return(&notation_material, "mem6/notation-addition", false, 2, 2)?;
    let rust_world = population_return(&rust_material, "mem6/rust-addition", false, 2, 2)?;
    let material_aperture = MaterialFactorizationAperture::found(&rest).map_err(display)?;
    let prose_factorization = material_aperture
        .factor(&prose_material, &prose_world)
        .map_err(display)?;
    let notation_factorization = material_aperture
        .factor(&notation_material, &notation_world)
        .map_err(display)?;
    let rust_factorization = material_aperture
        .factor(&rust_material, &rust_world)
        .map_err(display)?;
    let prose_notation = compare_material_factorizations(
        &prose_factorization,
        &notation_factorization,
        "mem6/naturality/prose-notation",
    );
    let prose_rust = compare_material_factorizations(
        &prose_factorization,
        &rust_factorization,
        "mem6/naturality/prose-rust",
    );
    let mathematics_operation_natural_across_codecs =
        prose_notation.square_commutes && prose_rust.square_commutes;

    let ambiguity_material = material(
        "mem6/material/equal-value-separator",
        b"two caused operations have one equal terminal population",
        "operation-separator-control",
    )?;
    let ambiguity_union =
        population_return(&ambiguity_material, "mem6/ambiguity-union", false, 2, 2)?;
    let ambiguity_product =
        population_return(&ambiguity_material, "mem6/ambiguity-product", true, 2, 2)?;
    let operation_separator = material_aperture
        .factor_candidates(&ambiguity_material, &[ambiguity_union, ambiguity_product])
        .map_err(display)?;
    let equal_value_operations_separated_by_successor = matches!(
        &operation_separator,
        MaterialFactorizationReturn::Insufficient(insufficiency)
            if insufficiency.candidate_sections.len() == 2
                && insufficiency.shortest_separator.left_returned_population
                    != insufficiency.shortest_separator.right_returned_population
    );

    // The raw optical potential and all of its alternative covers remain present.
    let optical = HierarchicalOpticalPassage::read(&fs::read(root.join(OPTICAL)).map_err(display)?)
        .map_err(display)?;
    let raw_optical = fs::read(root.join(OPTICAL_RAW)).map_err(display)?;
    let optical_material = AddressedMaterialOccurrence::found(
        "mem6/material/raw-optical",
        &raw_optical,
        None,
        vec!["encoded-raster".to_owned()],
        vec!["unresolved optical identities remain open".to_owned()],
    )
    .map_err(display)?;
    let constraint = unique_optical_constraint(&optical)?;
    let optical_world = population_return_from_addresses(
        &optical_material,
        "mem6/optical-constraint",
        false,
        constraint.before_member_addresses.clone(),
        constraint.after_member_addresses.clone(),
    )?;
    let optical_returns = [optical_world];
    let optical_candidates =
        HierarchicalOpticalMaterialCandidates::found(&optical_material, &optical, &optical_returns)
            .map_err(display)?;
    let optical_factored = material_aperture
        .factor_hierarchical_optical_candidates(&optical_candidates)
        .map_err(display)?;
    let optical_return = match &optical_factored {
        HierarchicalOpticalMaterialReturn::Supported {
            passage,
            bindings,
            factorization,
        } => json!({
            "status": "supported",
            "bindings": bindings,
            "native_operation_identity_sha256": factorization.native_operation_identity_sha256,
            "holon_population": passage.holons.len(),
            "alternative_cover_population": passage.alternative_covers.len(),
            "glyph_fibre_population": passage.native_consequence.equation_glyph_fibres.len(),
            "constraint_section_population": passage.native_consequence.equation_constraint_sections.len(),
            "open_exterior": passage.native_consequence.open_exterior,
        }),
        HierarchicalOpticalMaterialReturn::Insufficient {
            passage,
            bindings,
            material_return,
            open_identity,
        } => json!({
            "status": "insufficient",
            "bindings": bindings,
            "material_return": material_return,
            "holon_population": passage.holons.len(),
            "alternative_cover_population": passage.alternative_covers.len(),
            "glyph_fibre_population": passage.native_consequence.equation_glyph_fibres.len(),
            "constraint_section_population": passage.native_consequence.equation_constraint_sections.len(),
            "open_exterior": open_identity,
        }),
    };
    let optical_potential_fibre_retained = optical_return["holon_population"]
        .as_u64()
        .is_some_and(|population| population > 0)
        && optical_return["alternative_cover_population"]
            .as_u64()
            .is_some_and(|population| population > 0)
        && optical_return["glyph_fibre_population"]
            .as_u64()
            .is_some_and(|population| population > 0);

    let rust_source =
        realize_material_source(&rust_factorization, MaterialSourceCodec::Rust).map_err(display)?;
    let rust_path = output.join("04-returned-operation.rs");
    fs::write(&rust_path, &rust_source.payload).map_err(display)?;
    let rustc = run_rustc(&rust_path, &output.join("04-returned-operation.rlib"))?;
    let code_compiled_and_transition_atlas_returned = rustc.status.success()
        && !rust_factorization
            .mathematical_complex
            .operation_cells
            .is_empty()
        && !rust_factorization
            .mathematical_complex
            .exact_consequence_faces
            .is_empty()
        && rust_source.native_operation_identity_sha256
            == rust_factorization.native_operation_identity_sha256;
    let code_return = json!({
        "realization": rust_source,
        "transition_complex": rust_factorization.mathematical_complex,
        "compiler": process_receipt(&rustc),
    });
    let material_naturality = json!({
        "prose_notation": prose_notation,
        "prose_rust": prose_rust,
        "prose_operation": prose_factorization.native_operation_identity_sha256,
        "notation_operation": notation_factorization.native_operation_identity_sha256,
        "rust_operation": rust_factorization.native_operation_identity_sha256,
    });
    let operation_separator = serde_json::to_value(&operation_separator).map_err(display)?;
    drop(optical_factored);
    drop(material_aperture);
    drop(prose_factorization);
    drop(notation_factorization);
    drop(rust_factorization);

    let acoustic =
        ExactAcousticOccurrence::read(&root.join(ACOUSTIC), "mem6/exterior/acoustic", 512, 256, 64)
            .map_err(display)?;
    let acoustic_before = serde_json::to_value(&acoustic).map_err(display)?;
    let radiation_aperture = NativeRadiationAperture::found(&rest).map_err(display)?;
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let (left_cell, shared_cell, disjoint_cell) = select_receiver_cells(rest.affine_cells())?;
    let unrelated_cell = rest
        .affine_cells()
        .iter()
        .find(|cell| {
            !radiation_aperture
                .relational_cell_addresses
                .contains(&cell.cell_address)
        })
        .map(|cell| cell.cell_address.clone())
        .ok_or_else(|| {
            "the integrated body has no participant-disjoint relational cell".to_owned()
        })?;
    let base = BaseUnits::declare(["athena-exterior-action"]).map_err(display)?;
    let dimension = base.unit("athena-exterior-action").map_err(display)?;
    let mut membrane = NativeCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;

    let participant_requests = [
        ("mem6/request/describe", "Describe Brandon."),
        ("mem6/request/identify", "Identify Brandon."),
        (
            "mem6/request/infer",
            "What can be inferred about Brandon from the laboratory's continuing history?",
        ),
    ];
    let mut native_sections = Vec::new();
    for (occurrence, surface) in participant_requests {
        let exterior =
            ExteriorActionCurrent::transduce(occurrence, surface.as_bytes()).map_err(display)?;
        native_sections.push(conduct_request(
            &mut membrane,
            &radiation_aperture,
            &native_address,
            receiver,
            &dimension,
            exterior,
            None,
        )?);
    }

    // Refinement is a real recurrence: the first inferred exterior surface returns through the
    // same rested membrane as later caused material.  The driver supplies no desired successor
    // surface; each later native section is determined before its renderer runs.
    let participant_rest = membrane.into_rest();
    let participant_surfaces = native_sections
        .iter()
        .cloned()
        .map(|section| {
            section
                .render(&participant_rest, &radiation_aperture)
                .map_err(display)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let returned_participant_surface = participant_surfaces
        .first()
        .ok_or_else(|| "the participant passage returned no exterior surface".to_owned())?;
    let refinement_inputs = [
        ("mem6/request/rewrite", "Rewrite Brandon."),
        ("mem6/request/compress", "Compress Brandon."),
        ("mem6/request/expand", "Expand Brandon."),
        ("mem6/request/revoice", "Revoice Brandon."),
    ];
    let mut refinement_recurrence = Vec::new();
    membrane = NativeCausalMembrane::mount(participant_rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    for (occurrence, surface) in &refinement_inputs {
        let exterior = ExteriorActionCurrent::transduce(*occurrence, surface.as_bytes())
            .and_then(|current| {
                current.after_returned(
                    returned_participant_surface.exterior_occurrence.clone(),
                    returned_participant_surface.text.as_bytes(),
                )
            })
            .map_err(display)?;
        let source_sha256 = exterior.source_sha256.clone();
        let returned_component_mounted = exterior.source_components.first().is_some_and(|source| {
            source.occurrence == returned_participant_surface.exterior_occurrence
                && source.source_sha256 == returned_participant_surface.text_sha256
        });
        let section = conduct_request(
            &mut membrane,
            &radiation_aperture,
            &native_address,
            receiver,
            &dimension,
            exterior,
            native_sections.first(),
        )?;
        refinement_recurrence.push(ReturnedRefinementReceipt {
            prior_radiation_identity_sha256: returned_participant_surface
                .radiation_identity_sha256
                .clone(),
            prior_surface_sha256: returned_participant_surface.text_sha256.clone(),
            refinement_occurrence: (*occurrence).to_owned(),
            refinement_source_sha256: source_sha256.clone(),
            same_rested_identity_sha256: rested_identity_sha256.clone(),
            returned_surface_was_mounted_as_exterior_material: returned_component_mounted
                && section.exterior_source_sha256 == source_sha256,
        });
        native_sections.push(section);
    }

    let shared_contact = membrane
        .conduct_resident_interior(
            &left_cell,
            &shared_cell,
            &ExactComplexWaveCurrent::new(rat(1), rat(1)),
        )
        .map_err(display)?;
    let disjoint_contact = membrane
        .conduct_resident_interior(
            &left_cell,
            &disjoint_cell,
            &ExactComplexWaveCurrent::new(rat(1), rat(1)),
        )
        .map_err(display)?;

    let mut common_membrane_crossings = Vec::new();
    common_membrane_crossings.push(cross_source(
        &mut membrane,
        prose_material,
        &native_address,
        receiver,
    )?);
    common_membrane_crossings.push(cross_source(
        &mut membrane,
        notation_material,
        &native_address,
        receiver,
    )?);
    common_membrane_crossings.push(cross_source(
        &mut membrane,
        rust_material,
        &native_address,
        receiver,
    )?);
    common_membrane_crossings.push(cross_source(
        &mut membrane,
        optical,
        &native_address,
        receiver,
    )?);
    let (acoustic_crossing, acoustic) =
        cross_source_recover(&mut membrane, acoustic, &native_address, receiver)?;
    common_membrane_crossings.push(acoustic_crossing);
    let acoustic_after = serde_json::to_value(&acoustic).map_err(display)?;
    let acoustic_exact_source_fibre_returned = acoustic_before == acoustic_after;
    let acoustic_return = json!({
        "exact_source_fibre_recovered": acoustic_exact_source_fibre_returned,
        "occurrence": acoustic_after,
    });
    let rest = membrane.into_rest();
    let mut participant_and_refinement_surfaces = participant_surfaces;
    participant_and_refinement_surfaces.extend(
        native_sections[3..]
            .iter()
            .cloned()
            .map(|section| section.render(&rest, &radiation_aperture).map_err(display))
            .collect::<Result<Vec<_>, _>>()?,
    );
    let receiver_faithful = |surface: &ExteriorRadiationSurface| {
        surface.text.to_lowercase().contains("brandon")
            && !surface.candidate_search_performed
            && !surface.stored_sentence_selected
            && !surface.expected_answer_consulted
    };
    let participant_surfaces_distinct_and_receiver_faithful = participant_and_refinement_surfaces
        [..3]
        .iter()
        .map(|surface| surface.text_sha256.as_str())
        .collect::<BTreeSet<_>>()
        .len()
        == 3
        && participant_and_refinement_surfaces[..3]
            .iter()
            .all(receiver_faithful);
    let refinement_surfaces_distinct_and_receiver_faithful = participant_and_refinement_surfaces
        [3..]
        .iter()
        .map(|surface| surface.text_sha256.as_str())
        .collect::<BTreeSet<_>>()
        .len()
        == 4
        && participant_and_refinement_surfaces[3..]
            .iter()
            .all(receiver_faithful);
    let refinements_are_caused_by_the_returned_participant_surface = refinement_recurrence.len()
        == 4
        && refinement_recurrence.iter().all(|receipt| {
            receipt.returned_surface_was_mounted_as_exterior_material
                && receipt.same_rested_identity_sha256 == rested_identity_sha256
                && receipt.prior_surface_sha256
                    == participant_and_refinement_surfaces[0].text_sha256
        });
    let shared_contact_nonzero_and_disjoint_control_zero =
        !shared_contact.native_radiation.is_zero() && disjoint_contact.native_radiation.is_zero();

    // Local interventions act on the already-returned body and restore it exactly.
    let baseline_section = native_sections[0].clone();
    let baseline_surface = participant_and_refinement_surfaces[0].clone();
    let target_cell = baseline_section
        .emitted_relational_cell_addresses
        .first()
        .cloned()
        .ok_or_else(|| "the baseline response emitted no native cell".to_owned())?;
    let (target_ablated, target_withdrawal) = rest
        .withdraw_relational_cell(&target_cell)
        .map_err(display)?;
    let (target_section, target_surface, target_ablated) = infer_once(
        target_ablated,
        participant_requests[0].0,
        participant_requests[0].1,
        &dimension,
    )?;
    let targeted_ablation_changed_response = target_section.emitted_relational_cell_addresses
        != baseline_section.emitted_relational_cell_addresses
        || target_surface.text != baseline_surface.text;
    let rest =
        ReturnedAffineLaboratoryRest::restore_relational_cell(target_ablated, target_withdrawal)
            .map_err(display)?;
    let (sibling_ablated, sibling_withdrawal) = rest
        .withdraw_relational_cell(&unrelated_cell)
        .map_err(display)?;
    let (sibling_section, sibling_surface, sibling_ablated) = infer_once(
        sibling_ablated,
        participant_requests[0].0,
        participant_requests[0].1,
        &dimension,
    )?;
    let unrelated_ablation_preserved_response = sibling_section.emitted_relational_cell_addresses
        == baseline_section.emitted_relational_cell_addresses
        && sibling_surface.text == baseline_surface.text;
    let rest =
        ReturnedAffineLaboratoryRest::restore_relational_cell(sibling_ablated, sibling_withdrawal)
            .map_err(display)?;
    let restored_identity = rest.identity().to_owned();
    let remounted =
        ReturnedAffineLaboratoryRest::read_admitted(&wire, &witness).map_err(display)?;
    let exact_restoration_and_source_detached_remount = restored_identity == rested_identity_sha256
        && remounted.identity() == rested_identity_sha256;

    let every_exterior_family_crossed_one_mouth = common_membrane_crossings.len() == 5
        && common_membrane_crossings
            .iter()
            .all(|receipt| receipt.rested_identity_sha256 == rested_identity_sha256);
    let internal_deed_or_semantic_mode_present = radiation_aperture.deed_or_semantic_mode_supplied;
    let lean_in_runtime = false;
    let expected_answer_or_surface_consulted = participant_and_refinement_surfaces
        .iter()
        .any(|surface| surface.expected_answer_consulted || surface.stored_sentence_selected);
    let pass = participant_surfaces_distinct_and_receiver_faithful
        && refinement_surfaces_distinct_and_receiver_faithful
        && refinements_are_caused_by_the_returned_participant_surface
        && mathematics_operation_natural_across_codecs
        && equal_value_operations_separated_by_successor
        && optical_potential_fibre_retained
        && acoustic_exact_source_fibre_returned
        && code_compiled_and_transition_atlas_returned
        && every_exterior_family_crossed_one_mouth
        && shared_contact_nonzero_and_disjoint_control_zero
        && targeted_ablation_changed_response
        && unrelated_ablation_preserved_response
        && exact_restoration_and_source_detached_remount
        && !internal_deed_or_semantic_mode_present
        && !lean_in_runtime
        && !expected_answer_or_surface_consulted;
    if !pass {
        write_json(
            output.join("00-integrated-membrane-release.json"),
            &json!({
                "truth_status": "counterexample",
                "evidence_tags": ["implemented-exact", "measured"],
                "rested_identity_sha256": rested_identity_sha256,
                "participant_and_refinement_surfaces": participant_and_refinement_surfaces,
                "native_sections": native_sections,
                "refinement_recurrence": refinement_recurrence,
                "participant_surfaces_distinct_and_receiver_faithful": participant_surfaces_distinct_and_receiver_faithful,
                "refinement_surfaces_distinct_and_receiver_faithful": refinement_surfaces_distinct_and_receiver_faithful,
                "refinements_are_caused_by_the_returned_participant_surface": refinements_are_caused_by_the_returned_participant_surface,
                "mathematics_operation_natural_across_codecs": mathematics_operation_natural_across_codecs,
                "equal_value_operations_separated_by_successor": equal_value_operations_separated_by_successor,
                "optical_potential_fibre_retained": optical_potential_fibre_retained,
                "acoustic_exact_source_fibre_returned": acoustic_exact_source_fibre_returned,
                "code_compiled_and_transition_atlas_returned": code_compiled_and_transition_atlas_returned,
                "every_exterior_family_crossed_one_mouth": every_exterior_family_crossed_one_mouth,
                "shared_contact_nonzero_and_disjoint_control_zero": shared_contact_nonzero_and_disjoint_control_zero,
                "targeted_ablation_changed_response": targeted_ablation_changed_response,
                "unrelated_ablation_preserved_response": unrelated_ablation_preserved_response,
                "exact_restoration_and_source_detached_remount": exact_restoration_and_source_detached_remount,
                "internal_deed_or_semantic_mode_present": internal_deed_or_semantic_mode_present,
                "lean_in_runtime": lean_in_runtime,
                "expected_answer_or_surface_consulted": expected_answer_or_surface_consulted,
                "shortest_obstruction": "the four returned refinements did not yet yield distinct receiver-faithful exterior surfaces inside the carried local affine star",
            }),
        )?;
        return Err(format!(
            "MEM6 refused: participant={participant_surfaces_distinct_and_receiver_faithful}, refinement={refinement_surfaces_distinct_and_receiver_faithful}, recurrence={refinements_are_caused_by_the_returned_participant_surface}, math={mathematics_operation_natural_across_codecs}, separator={equal_value_operations_separated_by_successor}, optical={optical_potential_fibre_retained}, acoustic={acoustic_exact_source_fibre_returned}, code={code_compiled_and_transition_atlas_returned}, mouth={every_exterior_family_crossed_one_mouth}, contact={shared_contact_nonzero_and_disjoint_control_zero}, target={targeted_ablation_changed_response}, sibling={unrelated_ablation_preserved_response}, restore={exact_restoration_and_source_detached_remount}, mode={internal_deed_or_semantic_mode_present}, expected={expected_answer_or_surface_consulted}"
        ));
    }
    let grade = Mem6Grade {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        rested_identity_sha256,
        participant_and_refinement_surfaces,
        refinement_recurrence,
        material_naturality,
        operation_separator,
        optical_return,
        acoustic_return,
        code_return,
        common_membrane_crossings,
        shared_contact,
        disjoint_contact,
        participant_surfaces_distinct_and_receiver_faithful,
        refinement_surfaces_distinct_and_receiver_faithful,
        refinements_are_caused_by_the_returned_participant_surface,
        mathematics_operation_natural_across_codecs,
        equal_value_operations_separated_by_successor,
        optical_potential_fibre_retained,
        acoustic_exact_source_fibre_returned,
        code_compiled_and_transition_atlas_returned,
        every_exterior_family_crossed_one_mouth,
        shared_contact_nonzero_and_disjoint_control_zero,
        targeted_ablation_changed_response,
        unrelated_ablation_preserved_response,
        exact_restoration_and_source_detached_remount,
        internal_deed_or_semantic_mode_present,
        lean_in_runtime,
        expected_answer_or_surface_consulted,
        open_exterior: vec![
            "the bounded receiver does not claim unrestricted conversational prose".to_owned(),
            "unseen optical, acoustic, mathematical, and code families remain open".to_owned(),
        ],
    };
    write_json(output.join("00-integrated-membrane-release.json"), &grade)?;
    for (at, surface) in grade.participant_and_refinement_surfaces.iter().enumerate() {
        fs::write(output.join(format!("01-surface-{at:02}.md")), &surface.text).map_err(display)?;
    }
    Ok(())
}

fn infer_once(
    rest: ReturnedAffineLaboratoryRest,
    occurrence: &str,
    surface: &str,
    dimension: &Dimension,
) -> Result<
    (
        NativeRadiationSection,
        ExteriorRadiationSurface,
        ReturnedAffineLaboratoryRest,
    ),
    String,
> {
    let aperture = NativeRadiationAperture::found(&rest).map_err(display)?;
    let (address, receiver) = continuing_native_address(&rest)?;
    let mut membrane = NativeCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let exterior =
        ExteriorActionCurrent::transduce(occurrence, surface.as_bytes()).map_err(display)?;
    let section = conduct_request(
        &mut membrane,
        &aperture,
        &address,
        receiver,
        dimension,
        exterior,
        None,
    )?;
    let rest = membrane.into_rest();
    let rendered = section.clone().render(&rest, &aperture).map_err(display)?;
    Ok((section, rendered, rest))
}

fn conduct_request<Standing: MembraneStanding>(
    membrane: &mut NativeCausalMembrane<Standing>,
    aperture: &NativeRadiationAperture,
    address: &life::native_intelligence::NativeSectionAddress,
    receiver: ReceiverId,
    dimension: &Dimension,
    exterior: ExteriorActionCurrent,
    predecessor: Option<&NativeRadiationSection>,
) -> Result<NativeRadiationSection, String> {
    let source = AddressedMaterialOccurrence::found(
        exterior.occurrence.clone(),
        exterior.exact_source_payload(),
        None,
        Vec::new(),
        vec!["later world consequence remains open".to_owned()],
    )
    .map_err(display)?;
    let fibre = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(fibre.address().event_projection.0);
    let occurrence = membrane
        .bind_occurrence(
            fibre,
            boundary,
            address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension.clone(),
                exterior.section.clone(),
                exterior.current.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("request binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err("the request did not cross the membrane".to_owned());
    };
    let receipt = returned.receipt.clone();
    returned
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|fibre| format!("the request source fibre was not exact: {fibre:?}"))?;
    let resident = membrane
        .conduct_resident_interior(
            &aperture.left_contact_cell,
            &aperture.right_contact_cell,
            &exterior.current,
        )
        .map_err(display)?;
    match predecessor {
        Some(predecessor) => NativeRadiationSection::found_after_returned(
            membrane.standing(),
            aperture,
            &exterior,
            &receipt,
            resident,
            predecessor,
        ),
        None => NativeRadiationSection::found(
            membrane.standing(),
            aperture,
            &exterior,
            &receipt,
            resident,
        ),
    }
    .map_err(display)
}

fn cross_source<T: ExteriorOccurrenceTransducer + Any + Send>(
    membrane: &mut NativeCausalMembrane<ReturnedAffineLaboratoryRest>,
    source: T,
    address: &life::native_intelligence::NativeSectionAddress,
    receiver: ReceiverId,
) -> Result<MembraneCrossingReceipt, String> {
    cross_source_recover(membrane, source, address, receiver).map(|(receipt, _)| receipt)
}

fn cross_source_recover<T: ExteriorOccurrenceTransducer + Any + Send>(
    membrane: &mut NativeCausalMembrane<ReturnedAffineLaboratoryRest>,
    source: T,
    address: &life::native_intelligence::NativeSectionAddress,
    receiver: ReceiverId,
) -> Result<(MembraneCrossingReceipt, T), String> {
    let exterior = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(exterior.address().event_projection.0);
    let base = BaseUnits::declare(["mem6-common-mouth-current"]).map_err(display)?;
    let occurrence = membrane
        .bind_occurrence(
            exterior,
            boundary,
            address,
            receiver,
            ExactMembraneChartPassage::identity(
                base.unit("mem6-common-mouth-current").map_err(display)?,
                ExactComplexWaveCurrent::zero(),
                ExactComplexWaveCurrent::zero(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("common-mouth binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err("the exterior source did not cross the common mouth".to_owned());
    };
    let receipt = returned.receipt;
    let source = returned
        .occurrence
        .exterior
        .recover::<T>()
        .map_err(|fibre| format!("the complete source fibre did not return: {fibre:?}"))?;
    Ok((receipt, source))
}

fn continuing_native_address(
    standing: &impl MembraneStanding,
) -> Result<(life::native_intelligence::NativeSectionAddress, ReceiverId), String> {
    for address in &standing.membrane_realization().sections {
        let addressed = standing
            .membrane_ecology()
            .native()
            .addressed_section(&address.spool, &address.thread, address.occurrence)
            .map_err(display)?;
        if addressed.thread().chronology.is_empty() {
            continue;
        }
        if let Some(receiver) = addressed.spool().receiver_family.iter().next().copied() {
            return Ok((address.clone(), receiver));
        }
    }
    Err("the body has no continuing addressed native section".to_owned())
}

fn select_receiver_cells(
    cells: &[life::native_intelligence::LaboratoryCellAffineSection],
) -> Result<(String, String, String), String> {
    let left = cells
        .first()
        .ok_or_else(|| "the affine ecology has no local cells".to_owned())?;
    let support = left
        .landmark_factors
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let shared = cells
        .iter()
        .skip(1)
        .find(|candidate| {
            candidate
                .landmark_factors
                .iter()
                .any(|factor| support.contains(factor))
        })
        .ok_or_else(|| "no distinct affine cell shares founded support".to_owned())?;
    let disjoint = cells
        .iter()
        .skip(1)
        .find(|candidate| {
            candidate
                .landmark_factors
                .iter()
                .all(|factor| !support.contains(factor))
        })
        .ok_or_else(|| "no disjoint affine sibling remains as a control".to_owned())?;
    Ok((
        left.cell_address.clone(),
        shared.cell_address.clone(),
        disjoint.cell_address.clone(),
    ))
}

fn unique_optical_constraint(
    optical: &HierarchicalOpticalPassage,
) -> Result<&life::mathematical_source::NativeEquationConstraintSection, String> {
    let mut populations = std::collections::BTreeMap::<(Vec<String>, Vec<String>), usize>::new();
    for section in &optical.native_consequence.equation_constraint_sections {
        *populations
            .entry((
                section.before_member_addresses.clone(),
                section.after_member_addresses.clone(),
            ))
            .or_default() += 1;
    }
    optical
        .native_consequence
        .equation_constraint_sections
        .iter()
        .find(|section| {
            populations.get(&(
                section.before_member_addresses.clone(),
                section.after_member_addresses.clone(),
            )) == Some(&1)
                && !section.before_member_addresses.is_empty()
                && !section.after_member_addresses.is_empty()
        })
        .ok_or_else(|| "no uniquely addressed optical constraint section is available".to_owned())
}

fn material(
    occurrence: &str,
    payload: &[u8],
    face: &str,
) -> Result<AddressedMaterialOccurrence, String> {
    AddressedMaterialOccurrence::found(
        occurrence,
        payload,
        None,
        vec![face.to_owned()],
        vec!["the exterior presentation remains outside native operation identity".to_owned()],
    )
    .map_err(display)
}

fn population_return(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    product: bool,
    left_population: usize,
    right_population: usize,
) -> Result<CausalOperationWorldReturn, String> {
    let left = (0..left_population)
        .map(|at| format!("{prefix}/left/{at}"))
        .collect::<Vec<_>>();
    let right = (0..right_population)
        .map(|at| format!("{prefix}/right/{at}"))
        .collect::<Vec<_>>();
    population_return_from_addresses(material, prefix, product, left, right)
}

fn population_return_from_addresses(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    product: bool,
    left: Vec<String>,
    right: Vec<String>,
) -> Result<CausalOperationWorldReturn, String> {
    let result_cells: Vec<CausalResultCell> = if product {
        left.iter()
            .flat_map(|left_member| {
                right.iter().map(move |right_member| CausalResultCell {
                    occurrence: format!("{prefix}/result/{left_member}/{right_member}"),
                    left_member: Some(left_member.clone()),
                    right_member: Some(right_member.clone()),
                })
            })
            .collect()
    } else {
        left.iter()
            .map(|member| CausalResultCell {
                occurrence: format!("{prefix}/result/left/{member}"),
                left_member: Some(member.clone()),
                right_member: None,
            })
            .chain(right.iter().map(|member| CausalResultCell {
                occurrence: format!("{prefix}/result/right/{member}"),
                left_member: None,
                right_member: Some(member.clone()),
            }))
            .collect()
    };
    let returned_payload = result_cells.len().to_string();
    let apparatus = ExteriorWorldReturnTestimony::found(
        format!("{prefix}/apparatus"),
        "causal-population-world-return",
        true,
        returned_payload.as_bytes(),
        vec!["successor histories outside the declared intervention remain open".to_owned()],
    )
    .map_err(display)?;
    CausalOperationWorldReturn::found(
        format!("{prefix}/return"),
        material.occurrence.clone(),
        left,
        right,
        result_cells,
        apparatus,
        vec!["later operation interventions remain open".to_owned()],
    )
    .map_err(display)
}

fn admitted_witness() -> Result<AdmittedReturnedAffineLaboratoryRestWitness, String> {
    AdmittedReturnedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)
}

fn run_rustc(source: &Path, output: &Path) -> Result<Output, String> {
    Command::new("rustc")
        .args(["--edition=2021", "--crate-type=lib"])
        .arg(source)
        .arg("-o")
        .arg(output)
        .output()
        .map_err(display)
}

fn process_receipt(output: &Output) -> Value {
    json!({
        "accepted": output.status.success(),
        "exit_code": output.status.code(),
        "stdout": String::from_utf8_lossy(&output.stdout),
        "stderr": String::from_utf8_lossy(&output.stderr),
        "returned_testimony_sha256": sha256(&[output.stdout.as_slice(), output.stderr.as_slice()].concat()),
    })
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = env::current_dir().map_err(display)?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("blueprint").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("could not locate the holonics workspace root".to_owned());
        }
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
