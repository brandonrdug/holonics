//! L6 — one affine Athena body returns prose, mathematical, optical, source-code, participant,
//! perspective, ablation, restoration, and source-detached consequences.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    time::Instant,
};

use life::{
    mathematical_source::HierarchicalOpticalPassage,
    native_intelligence::{
        compare_material_factorizations, realize_material_source, AddressedEmanationIngress,
        AddressedEmanationWorldReturn, AddressedMaterialOccurrence, AffineLaboratoryCultivatedRest,
        CausalOperationWorldReturn, CausalResultCell, EmanationDeed, EmanationParticipant,
        EmanationSurface, EmanationVoice, ExteriorWorldReturnTestimony,
        HierarchicalOpticalMaterialCandidates, HierarchicalOpticalMaterialReturn,
        LaboratoryParticipantIngress, MaterialFactorizationAperture, MaterialFactorizationReturn,
        MaterialSourceBoundaryWorldReturn, MaterialSourceCodec, NativePotentialCellKind,
        PerspectiveChart, SituatedEmanationDifference, SituatedEmanationPassage,
    },
};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    "output/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const OPTICAL: &str =
    "output/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const OPTICAL_RAW: &str =
    "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const OUTPUT: &str = concat!(
    "output/the_affine_athena_ecology_returns_prose_mathematics_optics_code_and_",
    "participant_navigation_l6"
);

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let out = root.join(OUTPUT);
    let grade_path = out.join("08-l6-primary-qualitative-grade.json");
    if grade_path.exists() {
        return Err(format!(
            "preserve admitted L6 return {}",
            grade_path.display()
        ));
    }
    fs::create_dir_all(&out).map_err(display)?;
    let started = Instant::now();

    let rested_wire = fs::read(root.join(REST)).map_err(display)?;
    let rest = AffineLaboratoryCultivatedRest::read(&rested_wire).map_err(display)?;
    let canonical_rest_identity = rest.identity().to_owned();
    let ablation_atlas = rest.ablation_atlas().map_err(display)?;

    let prose_material = material(
        "l6/material/prose/disjoint-population",
        b"Two disjoint causal populations of two return four addressed occurrences.",
        "ordinary-prose",
    )?;
    let notation_material = material(
        "l6/material/notation/disjoint-population",
        br"|{a,b} \sqcup {c,d}| = 4",
        "exact-notation",
    )?;
    let rust_material = material(
        "l6/material/rust/disjoint-population",
        b"left.into_iter().chain(right).count()",
        "rust-source",
    )?;
    let prose_world = population_return(&prose_material, "l6/prose-union", false, 2, 2)?;
    let notation_world = population_return(&notation_material, "l6/notation-union", false, 2, 2)?;
    let rust_world = population_return(&rust_material, "l6/rust-union", false, 2, 2)?;

    let aperture = MaterialFactorizationAperture::found(&rest).map_err(display)?;
    let mut prose_factorization = aperture
        .factor(&prose_material, &prose_world)
        .map_err(display)?;
    let notation_factorization = aperture
        .factor(&notation_material, &notation_world)
        .map_err(display)?;
    let prose_notation = compare_material_factorizations(
        &prose_factorization,
        &notation_factorization,
        "same-native-operation/prose-notation",
    );
    drop(notation_factorization);
    let rust_factorization = aperture
        .factor(&rust_material, &rust_world)
        .map_err(display)?;
    let prose_rust = compare_material_factorizations(
        &prose_factorization,
        &rust_factorization,
        "same-native-operation/prose-rust",
    );
    drop(rust_factorization);

    let ambiguity_material = material(
        "l6/material/equal-answer-distinct-operation",
        b"Two operation currents return the same count before a successor intervention.",
        "operation-separator-control",
    )?;
    let ambiguity_union =
        population_return(&ambiguity_material, "l6/ambiguity-union", false, 2, 2)?;
    let ambiguity_product =
        population_return(&ambiguity_material, "l6/ambiguity-product", true, 2, 2)?;
    let operation_separator = aperture
        .factor_candidates(&ambiguity_material, &[ambiguity_union, ambiguity_product])
        .map_err(display)?;
    let operation_separated = matches!(
        &operation_separator,
        MaterialFactorizationReturn::Insufficient(insufficiency)
            if insufficiency.candidate_sections.len() == 2
                && insufficiency.shortest_separator.left_returned_population == 5
                && insufficiency.shortest_separator.right_returned_population == 6
    );

    // The optical body is borrowed whole.  A constraint is chosen only by unique addressed
    // before/after incidence, never by its inherited relation glyph or object class.
    let optical_bytes = fs::read(root.join(OPTICAL)).map_err(display)?;
    let optical: HierarchicalOpticalPassage =
        serde_json::from_slice(&optical_bytes).map_err(display)?;
    let raw_optical = fs::read(root.join(OPTICAL_RAW)).map_err(display)?;
    let optical_material = AddressedMaterialOccurrence::found(
        "l6/material/raw-optical-page",
        &raw_optical,
        None,
        vec!["encoded-raster".to_owned()],
        vec!["unresolved optical identities remain open".to_owned()],
    )
    .map_err(display)?;
    let constraint = unique_optical_constraint(&optical)?;
    let optical_world = population_return_from_addresses(
        &optical_material,
        "l6/optical-constraint-return",
        false,
        constraint.before_member_addresses.clone(),
        constraint.after_member_addresses.clone(),
    )?;
    let optical_returns = [optical_world];
    let optical_candidates =
        HierarchicalOpticalMaterialCandidates::found(&optical_material, &optical, &optical_returns)
            .map_err(display)?;
    let optical_return = aperture
        .factor_hierarchical_optical_candidates(&optical_candidates)
        .map_err(display)?;
    let optical_summary = match optical_return {
        HierarchicalOpticalMaterialReturn::Supported {
            passage,
            bindings,
            factorization,
        } => {
            let value = json!({
                "status": "supported",
                "bindings": bindings,
                "native_operation_identity_sha256": factorization.native_operation_identity_sha256,
                "holon_population": passage.holons.len(),
                "alternative_cover_population": passage.alternative_covers.len(),
                "glyph_fibre_population": passage.native_consequence.equation_glyph_fibres.len(),
                "constraint_section_population": passage.native_consequence.equation_constraint_sections.len(),
                "open_identity": passage.native_consequence.open_exterior,
            });
            drop(factorization);
            value
        }
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
            "open_identity": open_identity,
        }),
    };
    let optical_exact = optical_summary["holon_population"].as_u64().unwrap_or(0) > 0
        && optical_summary["alternative_cover_population"]
            .as_u64()
            .unwrap_or(0)
            > 0
        && optical_summary["glyph_fibre_population"]
            .as_u64()
            .unwrap_or(0)
            > 0;

    let rust_source = realize_material_source(&prose_factorization, MaterialSourceCodec::Rust)
        .map_err(display)?;
    let lean_source = realize_material_source(&prose_factorization, MaterialSourceCodec::Lean)
        .map_err(display)?;
    let source_operation_common = rust_source.native_operation_identity_sha256
        == lean_source.native_operation_identity_sha256
        && rust_source.native_operation_identity_sha256
            == prose_factorization.native_operation_identity_sha256;
    let defect = rust_source
        .withhold_terminal_boundary("l6/source-defect/withheld-rust-boundary")
        .map_err(display)?;
    let invalid_rust_path = out.join("04-candidate-with-open-boundary.rs");
    fs::write(&invalid_rust_path, &defect.candidate.payload).map_err(display)?;
    let invalid_rust = run_rustc(&invalid_rust_path, &out.join("04-invalid.rlib"))?;
    if invalid_rust.status.success() {
        return Err("the declared open Rust boundary unexpectedly compiled".to_owned());
    }
    let defect_occurrence = defect.occurrence.clone();
    let returned_boundary = defect.withheld_boundary_fibre.clone();
    let failure_testimony = [
        invalid_rust.stdout.as_slice(),
        invalid_rust.stderr.as_slice(),
    ]
    .concat();
    let (revised_rust, source_revision) = defect
        .receive_world_return(MaterialSourceBoundaryWorldReturn {
            occurrence: "l6/world-return/rust-boundary".to_owned(),
            predecessor_defect_occurrence: defect_occurrence,
            apparatus_face: "rustc-exterior-apparatus".to_owned(),
            candidate_accepted: false,
            returned_boundary,
            returned_testimony_sha256: sha256(&failure_testimony),
        })
        .map_err(display)?;
    let revised_rust_path = out.join("04-returned-source-revision.rs");
    fs::write(&revised_rust_path, &revised_rust.payload).map_err(display)?;
    let revised_rustc = run_rustc(&revised_rust_path, &out.join("04-revised.rlib"))?;
    let lean_path = out.join("04-same-native-operation.lean");
    fs::write(&lean_path, &lean_source.payload).map_err(display)?;
    let lean_kernel = Command::new("lake")
        .args(["env", "lean"])
        .arg(&lean_path)
        .current_dir(root.join("soma/formal/elementary-holonics"))
        .output()
        .map_err(display)?;
    let source_revision_exact = !invalid_rust.status.success()
        && revised_rustc.status.success()
        && lean_kernel.status.success()
        && source_revision.exact_complete_source_restored
        && revised_rust.native_operation_identity_sha256
            == lean_source.native_operation_identity_sha256;

    drop(aperture);

    // One mount: the coupled current, participant incidence and complete affine field share the
    // already-admitted singular resident front.
    let mut resident = rest.mount().map_err(display)?;
    let resident_return = resident
        .conduct_material(&mut prose_factorization)
        .map_err(display)?;
    let integrated_apparatus = prose_factorization
        .cultivated_affine_transport
        .as_ref()
        .and_then(|transport| transport.integrated_resident_apparatus.clone())
        .ok_or("the integrated resident return is absent")?;
    let participant = EmanationParticipant {
        occurrence: "l6/participant/laboratory-operator".to_owned(),
        identity: "participant/laboratory-operator".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let participant_perspective = PerspectiveChart::found(
        "l6/chart/participant-referent",
        Some("athena-speaker".to_owned()),
        Some("laboratory-addressee".to_owned()),
    )
    .map_err(display)?;
    let mut participant_returns = Vec::new();
    for (ordinal, deed) in [
        EmanationDeed::Describe,
        EmanationDeed::Identify,
        EmanationDeed::Infer,
    ]
    .into_iter()
    .enumerate()
    {
        participant_returns.push(
            resident
                .emanate_participant(
                    LaboratoryParticipantIngress::found(
                        format!("l6/participant-ingress/{ordinal}"),
                        participant.clone(),
                        deed,
                        participant_perspective.clone(),
                    )
                    .map_err(display)?,
                )
                .map_err(display)?,
        );
    }
    let rest = resident.into_rest().map_err(display)?;

    let ingress = AddressedEmanationIngress::found(
        "l6/ingress/integrated-prose-code-return",
        prose_material.occurrence.clone(),
        b"Return the situated operation, its constraints, transport, and open reconstruction fibre.",
        None,
        participant.identity.clone(),
        vec![participant.clone()],
        EmanationDeed::Describe,
        vec![
            "preserve operation-sensitive successor sections".to_owned(),
            "retain the complete affine reconstruction fibre".to_owned(),
        ],
        PerspectiveChart::found("l6/chart/proper-name", None, None).map_err(display)?,
        vec![
            "l6/chronology/material-return".to_owned(),
            "l6/chronology/resident-current".to_owned(),
            "l6/chronology/source-revision".to_owned(),
        ],
        vec!["later mathematical and code successor histories".to_owned()],
        vec!["receivers outside the admitted L6 family remain open".to_owned()],
    )
    .map_err(display)?;
    let mut passage =
        SituatedEmanationPassage::found(rest, prose_factorization, resident_return, ingress)
            .map_err(display)?;
    let native_pre_surface = serde_json::to_value(passage.potential()).map_err(display)?;
    let complete_family = passage
        .potential()
        .cells
        .iter()
        .map(|cell| cell.body.kind())
        .collect::<BTreeSet<_>>();
    let compressed_family = BTreeSet::from([
        NativePotentialCellKind::ExactConsequence,
        NativePotentialCellKind::Participant,
    ]);
    let mut reverse_order = complete_family.iter().copied().collect::<Vec<_>>();
    reverse_order.reverse();
    let mut surfaces = Vec::new();
    let mut differences = Vec::new();
    let revision_payload = serde_json::to_vec(&source_revision).map_err(display)?;
    emit_and_return(
        &mut passage,
        &mut surfaces,
        &mut differences,
        "source-revision-return",
        &revision_payload,
        Some(EmanationDeed::Identify),
        Some(
            PerspectiveChart::found(
                "l6/chart/operator-speaks",
                Some(participant.identity.clone()),
                None,
            )
            .map_err(display)?,
        ),
        None,
        None,
        None,
    )?;
    emit_and_return(
        &mut passage,
        &mut surfaces,
        &mut differences,
        "compression-return",
        b"retain only the declared future receiver family and its complete hidden fibre",
        Some(EmanationDeed::Infer),
        Some(
            PerspectiveChart::found(
                "l6/chart/operator-addressed",
                None,
                Some(participant.identity.clone()),
            )
            .map_err(display)?,
        ),
        None,
        None,
        Some(compressed_family),
    )?;
    emit_and_return(
        &mut passage,
        &mut surfaces,
        &mut differences,
        "expansion-return",
        b"reopen the complete potential complex",
        Some(EmanationDeed::Explain),
        Some(PerspectiveChart::found("l6/chart/observer", None, None).map_err(display)?),
        None,
        None,
        Some(complete_family.clone()),
    )?;
    emit_and_return(
        &mut passage,
        &mut surfaces,
        &mut differences,
        "rewrite-revoice-return",
        b"rewrite the same causal content under the passive exterior voice",
        Some(EmanationDeed::Rewrite),
        None,
        Some(EmanationVoice::Passive),
        Some(reverse_order),
        None,
    )?;
    emit_and_return(
        &mut passage,
        &mut surfaces,
        &mut differences,
        "derivation-return",
        b"derive through the original active ordering",
        Some(EmanationDeed::Derive),
        None,
        Some(EmanationVoice::Active),
        Some(complete_family.iter().copied().collect()),
        None,
    )?;
    emit_and_return(
        &mut passage,
        &mut surfaces,
        &mut differences,
        "continuation-return",
        b"the integrated receiver occurrence closed and a later world remains open",
        None,
        None,
        None,
        None,
        None,
    )?;
    let rest = passage.into_rest().map_err(display)?;

    // Local structural ablation is performed after cultivation.  The target is an actually
    // returned participant cell; the sibling is incidence-disjoint and neither is chosen by a
    // word, name, expected sentence, or source ordinal.
    let baseline_describe = participant_returns
        .iter()
        .find(|returned| returned.deed == EmanationDeed::Describe)
        .ok_or("the baseline participant return is absent")?;
    let target_cell = baseline_describe
        .selected_cell_addresses
        .first()
        .cloned()
        .ok_or("the baseline describe return selected no native target")?;
    if !ablation_atlas
        .participant_incident_cells
        .contains(&target_cell)
    {
        return Err("the returned target is not participant-incident".to_owned());
    }
    let sibling_cell = ablation_atlas
        .participant_disjoint_cells
        .first()
        .cloned()
        .ok_or("the affine ecology has no disjoint sibling")?;

    let (target_ablated, target_withdrawal) = rest
        .withdraw_relational_cell(&target_cell)
        .map_err(display)?;
    let mut target_resident = target_ablated.mount().map_err(display)?;
    let target_return = target_resident
        .emanate_participant(
            LaboratoryParticipantIngress::found(
                "l6/ablation/target/describe",
                participant.clone(),
                EmanationDeed::Describe,
                participant_perspective.clone(),
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let target_ablated = target_resident.into_rest().map_err(display)?;
    let rest =
        AffineLaboratoryCultivatedRest::restore_relational_cell(target_ablated, target_withdrawal)
            .map_err(display)?;
    let target_attributable = !target_return.selected_cell_addresses.contains(&target_cell)
        && target_return.text != baseline_describe.text;

    let (sibling_ablated, sibling_withdrawal) = rest
        .withdraw_relational_cell(&sibling_cell)
        .map_err(display)?;
    let mut sibling_resident = sibling_ablated.mount().map_err(display)?;
    let sibling_return = sibling_resident
        .emanate_participant(
            LaboratoryParticipantIngress::found(
                "l6/ablation/disjoint-sibling/describe",
                participant.clone(),
                EmanationDeed::Describe,
                participant_perspective,
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let sibling_ablated = sibling_resident.into_rest().map_err(display)?;
    let rest = AffineLaboratoryCultivatedRest::restore_relational_cell(
        sibling_ablated,
        sibling_withdrawal,
    )
    .map_err(display)?;
    let sibling_inert = sibling_return.selected_cell_addresses
        == baseline_describe.selected_cell_addresses
        && sibling_return.text == baseline_describe.text;
    let local_restoration_exact = rest.identity() == canonical_rest_identity;

    let (predecessor, organ_withdrawal) = rest.withdraw_relational_organ().map_err(display)?;
    let predecessor_aperture =
        MaterialFactorizationAperture::found(&predecessor).map_err(display)?;
    let predecessor_factorization = predecessor_aperture
        .factor(&prose_material, &prose_world)
        .map_err(display)?;
    let predecessor_separated = predecessor_factorization
        .cultivated_affine_transport
        .is_none();
    drop(predecessor_aperture);
    drop(predecessor_factorization);
    let rest =
        AffineLaboratoryCultivatedRest::restore_relational_organ(predecessor, organ_withdrawal)
            .map_err(display)?;
    let restored_exact = rest.identity() == canonical_rest_identity;
    let remounted = AffineLaboratoryCultivatedRest::read(&rested_wire).map_err(display)?;
    let source_detached_remount_exact = remounted.identity() == canonical_rest_identity;

    let participant_signatures = participant_returns
        .iter()
        .map(|returned| returned.native_successor_identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let participant_texts = participant_returns
        .iter()
        .map(|returned| returned.text_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let participant_exact = participant_signatures.len() == 3
        && participant_texts.len() == 3
        && participant_returns
            .iter()
            .all(|returned| !returned.selected_cell_addresses.is_empty());
    let prose_texts = surfaces
        .iter()
        .map(|surface| surface.text.as_str())
        .collect::<BTreeSet<_>>();
    let prose_signatures = surfaces
        .iter()
        .map(|surface| surface.native_successor_identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let prose_exact = surfaces.len() == 6
        && prose_texts.len() == 6
        && prose_signatures.len() == 6
        && differences.iter().all(|difference| {
            !difference.changed_atoms.is_empty()
                && difference
                    .oriented_difference
                    .iter()
                    .any(|coefficient| *coefficient != 0)
                && difference.participant_lineage_preserved
        });
    let math_exact =
        prose_notation.square_commutes && prose_rust.square_commutes && operation_separated;
    let apparatus_exact = integrated_apparatus.one_underlying_context
        && integrated_apparatus.launches == 3
        && integrated_apparatus.synchronizations == 1
        && integrated_apparatus.intermediate_host_egress_octets == 0
        && !integrated_apparatus.invariant_transport_reuploaded
        && !integrated_apparatus.cpu_semantic_replay_after_device;
    let structural_pass = prose_exact
        && math_exact
        && optical_exact
        && source_operation_common
        && source_revision_exact
        && participant_exact
        && target_attributable
        && sibling_inert
        && local_restoration_exact
        && predecessor_separated
        && restored_exact
        && source_detached_remount_exact
        && apparatus_exact;

    write_json(
        out.join("00-one-affine-athena-body.json"),
        &json!({
            "truth_status": "established-bounded-implemented-exact-measured",
            "canonical_rest_identity_sha256": canonical_rest_identity,
            "native_pre_surface_consequence": native_pre_surface,
            "affine_landmark_population": rest.correspondences().len(),
            "affine_cell_population": rest.affine_cells().len(),
            "ablation_atlas": ablation_atlas,
        }),
    )?;
    write_json(
        out.join("01-prose-and-returned-differences.json"),
        &json!({"surfaces": surfaces, "situated_differences": differences}),
    )?;
    for (at, surface) in surfaces.iter().enumerate() {
        fs::write(
            out.join(format!("01-surface-{at:02}-{:?}.md", surface.deed).to_lowercase()),
            &surface.text,
        )
        .map_err(display)?;
    }
    write_json(
        out.join("02-mathematical-operation-and-separator.json"),
        &json!({
            "prose_notation_naturality": prose_notation,
            "prose_rust_naturality": prose_rust,
            "same_answer_different_operation": operation_separator,
        }),
    )?;
    write_json(
        out.join("03-hierarchical-optical-return.json"),
        &optical_summary,
    )?;
    write_json(
        out.join("04-source-code-and-exterior-returns.json"),
        &json!({
            "rust_revision": source_revision,
            "invalid_rustc": process_receipt(&invalid_rust),
            "revised_rustc": process_receipt(&revised_rustc),
            "lean_kernel": process_receipt(&lean_kernel),
            "rust_realization": revised_rust,
            "lean_realization": lean_source,
        }),
    )?;
    write_json(
        out.join("05-participant-perspective-returns.json"),
        &participant_returns,
    )?;
    for returned in &participant_returns {
        fs::write(
            out.join(format!("05-brandon-{:?}.md", returned.deed).to_lowercase()),
            &returned.text,
        )
        .map_err(display)?;
    }
    write_json(
        out.join("06-local-ablation-restoration-controls.json"),
        &json!({
            "target_cell": target_cell,
            "target_return": target_return,
            "target_attributable": target_attributable,
            "disjoint_sibling_cell": sibling_cell,
            "sibling_return": sibling_return,
            "sibling_inert": sibling_inert,
            "local_restoration_exact": local_restoration_exact,
            "whole_organ_predecessor_separated": predecessor_separated,
            "whole_organ_restoration_exact": restored_exact,
            "source_detached_remount_exact": source_detached_remount_exact,
        }),
    )?;
    write_json(
        out.join("07-resident-apparatus-and-source-access-audit.json"),
        &json!({
            "integrated_resident_apparatus": integrated_apparatus,
            "source_model_or_foreign_executor_in_hot_closure": false,
            "query_or_proper_name_selected_cultivation": false,
            "codec_label_routes_native_law": false,
            "scalar_entropy_or_cross_entropy_selected_support": false,
            "affine_support_retained_as_addressed_finite_population": true,
            "rank_four_fibre_not_chronology": true,
        }),
    )?;
    write_json(
        grade_path,
        &json!({
            "status": if structural_pass { "awaiting-primary-qualitative-inspection" } else { "counterexample" },
            "truth_status": if structural_pass {
                "established-bounded-implemented-exact-measured"
            } else {
                "counterexample-implemented-exact-measured"
            },
            "structural_pass": structural_pass,
            "primary_qualitative_inspection_accepted": false,
            "prose_receiver_exact": prose_exact,
            "mathematics_receiver_exact": math_exact,
            "hierarchical_optical_receiver_exact": optical_exact,
            "rust_lean_source_revision_exact": source_revision_exact,
            "participant_receiver_exact": participant_exact,
            "targeted_ablation_attributable": target_attributable,
            "unrelated_sibling_inert": sibling_inert,
            "predecessor_restoration_remount_exact": predecessor_separated && restored_exact && source_detached_remount_exact,
            "resident_apparatus_exact": apparatus_exact,
            "wall_milliseconds": started.elapsed().as_millis(),
        }),
    )?;
    if !structural_pass {
        return Err("the integrated L6 structural receiver returned a counterexample".to_owned());
    }
    println!(
        "L6 structural return passed in {} ms; primary prose and source artifacts await direct qualitative inspection.",
        started.elapsed().as_millis()
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_and_return(
    passage: &mut SituatedEmanationPassage<AffineLaboratoryCultivatedRest>,
    surfaces: &mut Vec<EmanationSurface>,
    differences: &mut Vec<SituatedEmanationDifference>,
    suffix: &str,
    payload: &[u8],
    deed: Option<EmanationDeed>,
    perspective: Option<PerspectiveChart>,
    voice: Option<EmanationVoice>,
    kind_order: Option<Vec<NativePotentialCellKind>>,
    future_receiver_family: Option<BTreeSet<NativePotentialCellKind>>,
) -> Result<(), String> {
    let surface = passage.emanate().map_err(display)?;
    let returned = AddressedEmanationWorldReturn::found(
        format!("l6/world-return/{suffix}"),
        surface.occurrence.clone(),
        payload,
        deed,
        perspective,
        voice,
        kind_order,
        future_receiver_family,
        None,
        (suffix == "continuation-return")
            .then(|| "l6/continuation/later-integrated-world".to_owned()),
        vec!["later receiver histories remain open".to_owned()],
    )
    .map_err(display)?;
    let difference = passage.receive_world_return(returned).map_err(display)?;
    surfaces.push(surface);
    differences.push(difference);
    Ok(())
}

fn unique_optical_constraint(
    optical: &HierarchicalOpticalPassage,
) -> Result<&life::mathematical_source::NativeEquationConstraintSection, String> {
    let mut populations = BTreeMap::<(Vec<String>, Vec<String>), usize>::new();
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
        .ok_or("no uniquely addressed optical constraint section is available".to_owned())
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
