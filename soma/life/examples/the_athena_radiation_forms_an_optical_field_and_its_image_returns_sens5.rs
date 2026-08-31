//! SENS5 receiver: native Athena radiation forms an exact multi-scale optical field before a
//! raster exists; cold image projections return through the GPU optical transducer and cultivate
//! the same acoustic-and-optical Athena body.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
};

use holonic_engine::{
    cuda_refine::{CudaRefineExecutor, ResidentMembraneInteriorReturn},
    image::{ExactRaster, ExactRgb, ImageExtent},
    quantity::BaseUnits,
    receiver_exact_compression::ReceiverId,
    BoundaryId, ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use image::ImageReader;
use life::{
    athena_native::{
        AcousticAthenaRest, AddressedMaterialOccurrence, AthenaCausalMembrane,
        AthenaMembraneConsequence, AthenaMembraneStanding, ExactMembraneChartPassage,
        ExteriorOccurrenceTransducer, MembraneCultivationReceipt, NativeAcousticRadiationInput,
        NativeOpticalCultivationReceipt, NativeOpticalRasterProjection,
        NativeOpticalReceiverIntervention, NativeOpticalStandingMutation, OpticalAthenaRest,
        StagedMembraneCultivation,
    },
    mathematical_source::{
        grow_optical_holons, recover_optical_passage, ExactOpticalOccurrence,
        HierarchicalOpticalPassage, OpticalHolonIntervention, OpticalPassage,
    },
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const SENS4: &str =
    "output/the_athena_radiation_becomes_voice_and_its_room_return_cultivates_the_body_sens4";
const OUTPUT: &str =
    "output/the_athena_radiation_forms_an_optical_field_and_its_image_returns_sens5";

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens5FoundationWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_rest_identity_sha256: String,
    optical_rest_identity_sha256: String,
    optical_rest_wire_sha256: String,
    cultivation: NativeOpticalCultivationReceipt,
    primary_field_identity_sha256: String,
    held_out_field_identity_sha256: String,
    primary_png_sha256: String,
    held_out_png_sha256: String,
    width_cells: u32,
    height_cells: u32,
    scale_spans: Vec<u32>,
    native_cell_population: usize,
    native_cover_population: usize,
    alternative_cover_population: usize,
    richer_receiver_reopening_population: usize,
    distinct_fields_before_rendering: bool,
    distinct_images_after_rendering: bool,
    held_out_section_absent_from_cultivation: bool,
    source_current_absent_from_morphology: bool,
    source_image_absent_from_morphology: bool,
    pixel_template_absent: bool,
    label_route_absent: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens5InterventionWitness {
    field_identity_sha256: String,
    baseline_projection_identity_sha256: String,
    projections: Vec<NativeOpticalRasterProjection>,
    projection_identities_pairwise_distinct: bool,
    png_identities_pairwise_distinct: bool,
    every_projection_retains_complete_field_fibre: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct OpticalWorldReturnSummary {
    name: String,
    field_identity_sha256: String,
    projection_identity_sha256: String,
    png_sha256: String,
    raw_occurrence: String,
    raw_component_population: usize,
    raw_relation_population: usize,
    raw_ambiguity_population: usize,
    hierarchy_occurrence: String,
    hierarchy_holon_population: usize,
    hierarchy_incidence_population: usize,
    hierarchy_alternative_cover_population: usize,
    resident_receiver_current: ExactComplexWaveCurrent,
    membrane_exterior_occurrence: String,
    complete_source_fibre_returned: bool,
    resident_gpu_launches: u64,
    resident_gpu_synchronizations: u64,
    cpu_semantic_fallback: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens5OpticalReturnWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    returns: Vec<OpticalWorldReturnSummary>,
    intervention_returns_attributable: bool,
    all_rendered_surfaces_crossed_existing_optical_transducer: bool,
    all_hot_optical_contacts_resident: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens5CultivatedReturnWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_rest_identity_sha256: String,
    successor_rest_identity_sha256: String,
    successor_body_identity_sha256: String,
    successor_wire_sha256: String,
    production_morphology_identity_sha256: String,
    returned_png_sha256: String,
    returned_hierarchy_identity_sha256: String,
    resident_receiver_current: ExactComplexWaveCurrent,
    resident_return_before_cultivation: ResidentMembraneInteriorReturn,
    cultivation: MembraneCultivationReceipt,
    complete_generated_optical_source_crossed: bool,
    same_body_identity_changed_after_optical_return: bool,
    production_morphology_preserved_after_optical_return: bool,
    later_conduct_changed_after_optical_return: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens5VerificationWitness {
    successor_remounted_exactly: bool,
    primary_field_reproduced_after_world_return: bool,
    held_out_field_reproduced_after_world_return: bool,
    primary_image_reproduced_after_world_return: bool,
    held_out_image_reproduced_after_world_return: bool,
    primary_and_held_out_remain_distinct: bool,
    targeted_optical_withdrawal_removed_owner: bool,
    targeted_optical_restoration_exact: bool,
    unrelated_acoustic_withdrawal_restored_exactly: bool,
    unrelated_acoustic_sibling_did_not_change_optical_conduct: bool,
    generated_source_image_absent_from_rested_morphology: bool,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens5Return {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    predecessor_rest_identity_sha256: String,
    optical_foundation_identity_sha256: String,
    cultivated_successor_identity_sha256: String,
    native_cell_population: usize,
    native_cover_population: usize,
    alternative_cover_population: usize,
    richer_receiver_reopening_population: usize,
    distinct_native_fields_before_rendering: bool,
    distinct_images_after_rendering: bool,
    crop_scale_color_chart_and_occlusion_returned: bool,
    all_intervention_differences_attributable: bool,
    held_out_not_copied_from_cultivation: bool,
    source_detached_remount_reproduced_production: bool,
    targeted_optical_ablation_removed_owner: bool,
    targeted_optical_restoration_exact: bool,
    unrelated_acoustic_sibling_invariant: bool,
    physical_optical_return_changed_same_body_identity: bool,
    physical_optical_return_changed_later_conduct: bool,
    external_image_generator_called: bool,
    stored_image_or_pixel_template_applied: bool,
    label_route_applied: bool,
    cpu_semantic_replay_after_device: bool,
    output_files: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    match env::var("SENS5_MODE").as_deref() {
        Ok("transduce") => transduce_phase(&root),
        Ok("return") => return_phase(&root),
        Ok("verify") => verify_phase(&root),
        Ok("grade") => grade_phase(&root),
        Ok("found") | Err(_) => foundation_phase(&root),
        Ok(other) => Err(format!("unknown SENS5_MODE {other}")),
    }
}

fn foundation_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    let primary = NativeAcousticRadiationInput::read(
        &fs::read(root.join(SENS4).join("01-primary-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held_out = NativeAcousticRadiationInput::read(
        &fs::read(root.join(SENS4).join("02-held-out-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let acoustic = AcousticAthenaRest::read(
        &fs::read(
            root.join(SENS4)
                .join("athena-acoustic-room-cultivated.rest"),
        )
        .map_err(display)?,
    )
    .map_err(display)?;
    let predecessor_rest_identity_sha256 = acoustic.identity().to_owned();
    let (rest, cultivation) = OpticalAthenaRest::cultivate(acoustic, &primary).map_err(display)?;
    let primary_field = rest.radiate(&primary).map_err(display)?;
    let held_out_field = rest.radiate(&held_out).map_err(display)?;
    let distinct_fields_before_rendering = primary_field != held_out_field;
    let (primary_png, primary_projection) = primary_field
        .render_png(NativeOpticalReceiverIntervention::None)
        .map_err(display)?;
    let (held_out_png, held_out_projection) = held_out_field
        .render_png(NativeOpticalReceiverIntervention::None)
        .map_err(display)?;
    let distinct_images_after_rendering = primary_png != held_out_png;
    if !distinct_fields_before_rendering || !distinct_images_after_rendering {
        return Err("distinct native radiation collapsed at the optical boundary".to_owned());
    }

    let interventions = [
        primary_field.derived_crop().map_err(display)?,
        primary_field.derived_scale().map_err(display)?,
        primary_field.derived_color_chart().map_err(display)?,
        primary_field.derived_occlusion().map_err(display)?,
    ];
    let names = ["crop", "scale", "color-chart", "occlusion"];
    let mut projections = Vec::new();
    let mut png_digests = Vec::new();
    for (name, intervention) in names.into_iter().zip(interventions) {
        let (png, projection) = primary_field.render_png(intervention).map_err(display)?;
        fs::write(
            output.join(format!("1{}-{name}.png", projections.len())),
            &png,
        )
        .map_err(display)?;
        png_digests.push(sha256(&png));
        projections.push(projection);
    }
    let projection_identities = projections
        .iter()
        .map(|projection| projection.identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let png_identities = png_digests
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let intervention_witness = Sens5InterventionWitness {
        field_identity_sha256: primary_field.identity_sha256.clone(),
        baseline_projection_identity_sha256: primary_projection.identity_sha256.clone(),
        projection_identities_pairwise_distinct: projection_identities.len() == projections.len()
            && !projection_identities.contains(primary_projection.identity_sha256.as_str()),
        png_identities_pairwise_distinct: png_identities.len() == projections.len()
            && !png_identities.contains(primary_projection.png_sha256.as_str()),
        every_projection_retains_complete_field_fibre: projections
            .iter()
            .all(|projection| projection.complete_field_reconstruction_fibre_retained),
        projections,
    };
    if !intervention_witness.projection_identities_pairwise_distinct
        || !intervention_witness.png_identities_pairwise_distinct
        || !intervention_witness.every_projection_retains_complete_field_fibre
    {
        return Err(
            "the optical receiver interventions did not return distinct attributable projections"
                .to_owned(),
        );
    }

    let rest_wire = rest.canonical_bytes().map_err(display)?;
    fs::write(output.join("athena-optical-production.rest"), &rest_wire).map_err(display)?;
    write_json(&output.join("01-primary-native-radiation.json"), &primary)?;
    write_json(&output.join("02-held-out-native-radiation.json"), &held_out)?;
    write_json(
        &output.join("03-primary-native-optical-field.json"),
        &primary_field,
    )?;
    write_json(
        &output.join("04-held-out-native-optical-field.json"),
        &held_out_field,
    )?;
    write_json(
        &output.join("05-primary-raster-projection.json"),
        &primary_projection,
    )?;
    write_json(
        &output.join("06-held-out-raster-projection.json"),
        &held_out_projection,
    )?;
    fs::write(output.join("07-primary-native-optical.png"), &primary_png).map_err(display)?;
    fs::write(output.join("08-held-out-native-optical.png"), &held_out_png).map_err(display)?;
    write_json(
        &output.join("14-intervention-projections.json"),
        &intervention_witness,
    )?;

    let witness = Sens5FoundationWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_rest_identity_sha256,
        optical_rest_identity_sha256: rest.identity().to_owned(),
        optical_rest_wire_sha256: sha256(&rest_wire),
        cultivation,
        primary_field_identity_sha256: primary_field.identity_sha256.clone(),
        held_out_field_identity_sha256: held_out_field.identity_sha256.clone(),
        primary_png_sha256: primary_projection.png_sha256.clone(),
        held_out_png_sha256: held_out_projection.png_sha256.clone(),
        width_cells: primary_field.width_cells,
        height_cells: primary_field.height_cells,
        scale_spans: rest.production().scale_spans.clone(),
        native_cell_population: primary_field.cells.len(),
        native_cover_population: primary_field.scale_covers.len(),
        alternative_cover_population: primary_field.alternative_covers.len(),
        richer_receiver_reopening_population: primary_field
            .alternative_covers
            .iter()
            .filter(|cover| cover.richer_receiver_reopens)
            .count(),
        distinct_fields_before_rendering,
        distinct_images_after_rendering,
        held_out_section_absent_from_cultivation: rest
            .production()
            .founding_radiation_identity_sha256
            != held_out.identity_sha256,
        source_current_absent_from_morphology: !rest.production().source_current_retained,
        source_image_absent_from_morphology: !rest.production().source_image_retained,
        pixel_template_absent: !rest.production().pixel_template_retained,
        label_route_absent: !rest.production().label_route_retained,
    };
    write_json(&output.join("09-foundation-witness.json"), &witness)?;
    eprintln!(
        "sens5 foundation: {} cells, {} covers, {} reopening fibres",
        witness.native_cell_population,
        witness.native_cover_population,
        witness.richer_receiver_reopening_population
    );
    Ok(())
}

fn transduce_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let rest = OpticalAthenaRest::read(
        &fs::read(output.join("athena-optical-production.rest")).map_err(display)?,
    )
    .map_err(display)?;
    let intervention: Sens5InterventionWitness = serde_json::from_slice(
        &fs::read(output.join("14-intervention-projections.json")).map_err(display)?,
    )
    .map_err(display)?;
    let primary_projection: NativeOpticalRasterProjection = serde_json::from_slice(
        &fs::read(output.join("05-primary-raster-projection.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held_projection: NativeOpticalRasterProjection = serde_json::from_slice(
        &fs::read(output.join("06-held-out-raster-projection.json")).map_err(display)?,
    )
    .map_err(display)?;
    let specifications = vec![
        (
            "primary".to_owned(),
            output.join("07-primary-native-optical.png"),
            primary_projection,
        ),
        (
            "held-out".to_owned(),
            output.join("08-held-out-native-optical.png"),
            held_projection,
        ),
        (
            "crop".to_owned(),
            output.join("10-crop.png"),
            intervention.projections[0].clone(),
        ),
        (
            "scale".to_owned(),
            output.join("11-scale.png"),
            intervention.projections[1].clone(),
        ),
        (
            "color-chart".to_owned(),
            output.join("12-color-chart.png"),
            intervention.projections[2].clone(),
        ),
        (
            "occlusion".to_owned(),
            output.join("13-occlusion.png"),
            intervention.projections[3].clone(),
        ),
    ];
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let dimension = BaseUnits::declare(["physical-optical-return-current"])
        .map_err(display)?
        .unit("physical-optical-return-current")
        .map_err(display)?;
    let mut membrane = AthenaCausalMembrane::mount(rest);
    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let mut returns = Vec::new();
    for (ordinal, (name, path, projection)) in specifications.into_iter().enumerate() {
        let png = fs::read(&path).map_err(display)?;
        if sha256(&png) != projection.png_sha256 {
            return Err(format!("{name} projection bytes changed"));
        }
        let (raw, hierarchy) = recover_hierarchy(&mut card, &name, &png)?;
        let raw_path = output.join(format!("{:02}-{name}-raw-optical.json", 15 + ordinal * 2));
        let hierarchy_path = output.join(format!(
            "{:02}-{name}-hierarchical-optical.json",
            16 + ordinal * 2
        ));
        write_json(&raw_path, &raw)?;
        write_json(&hierarchy_path, &hierarchy)?;
        let resident_receiver_current = optical_receiver_current(&raw, &hierarchy)?;
        let expected_source_sha256 = hierarchy.predecessor_source_sha256.clone();
        let expected_hierarchy_sha256 = sha256(&hierarchy.canonical_bytes().map_err(display)?);
        let occurrence = ExactOpticalOccurrence::found(
            format!("sens5/returned-generated-optical/{name}"),
            format!("memory://sens5/{name}"),
            png,
            hierarchy,
        )
        .map_err(display)?;
        let source_fibre = occurrence.into_exterior_fibre().map_err(display)?;
        let boundary = BoundaryId(source_fibre.address().event_projection.0);
        let exterior_occurrence = source_fibre.address().occurrence.clone();
        let bound = membrane
            .bind_occurrence(
                source_fibre,
                boundary,
                &native_address,
                receiver,
                ExactMembraneChartPassage::identity(
                    dimension.clone(),
                    ExactComplexWaveCurrent::zero(),
                    resident_receiver_current.clone(),
                ),
                Vec::new(),
            )
            .map_err(|failure| format!("{name} optical binding refused: {failure:?}"))?;
        let AthenaMembraneConsequence::Returned(returned) =
            membrane.receive_occurrence(bound).map_err(display)?
        else {
            return Err(format!("{name} optical surface did not cross"));
        };
        let recovered = returned
            .occurrence
            .exterior
            .recover::<ExactOpticalOccurrence>()
            .map_err(|_| format!("{name} source fibre did not return"))?;
        let complete_source_fibre_returned = recovered.source_sha256 == expected_source_sha256
            && sha256(&recovered.hierarchy.canonical_bytes().map_err(display)?)
                == expected_hierarchy_sha256;
        returns.push(OpticalWorldReturnSummary {
            name,
            field_identity_sha256: projection.field_identity_sha256,
            projection_identity_sha256: projection.identity_sha256,
            png_sha256: projection.png_sha256,
            raw_occurrence: raw.occurrence,
            raw_component_population: raw.components.len(),
            raw_relation_population: raw.relations.len(),
            raw_ambiguity_population: raw.ambiguity_fibres.len(),
            hierarchy_occurrence: recovered.hierarchy.occurrence,
            hierarchy_holon_population: recovered.hierarchy.holons.len(),
            hierarchy_incidence_population: recovered.hierarchy.incidences.len(),
            hierarchy_alternative_cover_population: recovered.hierarchy.alternative_covers.len(),
            resident_receiver_current,
            membrane_exterior_occurrence: exterior_occurrence,
            complete_source_fibre_returned,
            resident_gpu_launches: raw.device.launches,
            resident_gpu_synchronizations: raw.device.synchronizations,
            cpu_semantic_fallback: raw.device.cpu_semantic_fallback,
        });
    }
    let baseline = returns.first().ok_or("no optical return")?;
    let intervention_returns_attributable = returns.iter().skip(2).all(|returned| {
        returned.field_identity_sha256 == baseline.field_identity_sha256
            && returned.projection_identity_sha256 != baseline.projection_identity_sha256
            && returned.png_sha256 != baseline.png_sha256
            && returned.membrane_exterior_occurrence != baseline.membrane_exterior_occurrence
    });
    let witness = Sens5OpticalReturnWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        all_rendered_surfaces_crossed_existing_optical_transducer: returns
            .iter()
            .all(|returned| returned.complete_source_fibre_returned),
        all_hot_optical_contacts_resident: returns.iter().all(|returned| {
            returned.resident_gpu_launches >= 1
                && returned.resident_gpu_synchronizations >= 1
                && !returned.cpu_semantic_fallback
        }),
        intervention_returns_attributable,
        returns,
    };
    if !witness.intervention_returns_attributable
        || !witness.all_rendered_surfaces_crossed_existing_optical_transducer
        || !witness.all_hot_optical_contacts_resident
    {
        return Err("the generated optical surfaces did not return through one attributable resident boundary".to_owned());
    }
    write_json(
        &output.join("27-optical-world-return-witness.json"),
        &witness,
    )?;
    eprintln!(
        "sens5 transduce: six generated surfaces returned through the resident optical boundary"
    );
    Ok(())
}

fn return_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let returns: Sens5OpticalReturnWitness = serde_json::from_slice(
        &fs::read(output.join("27-optical-world-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let primary = returns
        .returns
        .first()
        .ok_or("the primary optical return is absent")?;
    let rest = OpticalAthenaRest::read(
        &fs::read(output.join("athena-optical-production.rest")).map_err(display)?,
    )
    .map_err(display)?;
    let predecessor_rest_identity_sha256 = rest.identity().to_owned();
    let production_morphology_identity_sha256 = rest.production().identity_sha256.clone();
    let hierarchy = HierarchicalOpticalPassage::read(
        &fs::read(output.join("16-primary-hierarchical-optical.json")).map_err(display)?,
    )
    .map_err(display)?;
    let png = fs::read(output.join("07-primary-native-optical.png")).map_err(display)?;
    let returned_hierarchy_identity_sha256 = sha256(&hierarchy.canonical_bytes().map_err(display)?);
    let occurrence = ExactOpticalOccurrence::found(
        "sens5/physical/generated-optical-return",
        "memory://sens5/primary-generated-optical",
        png,
        hierarchy,
    )
    .map_err(display)?;
    let complete_source_sha = occurrence.source_sha256.clone();
    let source_fibre = occurrence.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(source_fibre.address().event_projection.0);
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let (left, shared) = receiver_cells(rest.membrane_affine_cells())?;
    let dimension = BaseUnits::declare(["physical-optical-return-current"])
        .map_err(display)?
        .unit("physical-optical-return-current")
        .map_err(display)?;
    let injected = primary.resident_receiver_current.clone();
    let mut membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let bound = membrane
        .bind_occurrence(
            source_fibre,
            boundary,
            &native_address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension.clone(),
                ExactComplexWaveCurrent::zero(),
                injected.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("physical optical binding refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(initial_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the physical generated image did not cross".to_owned());
    };
    let recovered = initial_return
        .occurrence
        .exterior
        .recover::<ExactOpticalOccurrence>()
        .map_err(|_| "the complete generated image fibre did not return".to_owned())?;
    let complete_generated_optical_source_crossed = recovered.source_sha256 == complete_source_sha;
    let resident_return = membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    let world_payload = serde_json::to_vec(&(
        "sens5/returned-optical-world-consequence",
        &primary.png_sha256,
        &returned_hierarchy_identity_sha256,
        &resident_return.native_radiation,
        &resident_return.returned_radiation,
        &resident_return.family_overlaps,
    ))
    .map_err(display)?;
    let world_source = AddressedMaterialOccurrence::found(
        "sens5/world/returned-generated-optical-consequence",
        &world_payload,
        Some("sens5/physical/generated-optical-return".to_owned()),
        vec!["cold generated optical world return".to_owned()],
        vec!["later optical consequences remain open".to_owned()],
    )
    .map_err(display)?;
    let world_fibre = world_source.into_exterior_fibre().map_err(display)?;
    let world_boundary = BoundaryId(world_fibre.address().event_projection.0);
    let later = membrane
        .bind_occurrence(
            world_fibre,
            world_boundary,
            &native_address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension,
                resident_return.native_radiation.clone(),
                resident_return.returned_radiation.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("optical world return binding refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(world_return) =
        membrane.receive_occurrence(later).map_err(display)?
    else {
        return Err("the optical world consequence did not return".to_owned());
    };
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_return.clone())
        .map_err(display)?;
    let (rest, detached) = staged.detach().map_err(display)?;
    fs::write(
        output.join("28-detached-physical-optical-return.json"),
        detached.canonical_bytes().map_err(display)?,
    )
    .map_err(display)?;
    let (successor, cultivation, successor_wire) =
        detached.commit_restable(rest).map_err(display)?;
    let successor_rest_identity_sha256 = successor.identity().to_owned();
    let successor_body_identity_sha256 = successor.body().identity().to_owned();
    let same_body_identity_changed_after_optical_return =
        successor_rest_identity_sha256 != predecessor_rest_identity_sha256;
    let production_morphology_preserved_after_optical_return =
        successor.production().identity_sha256 == production_morphology_identity_sha256;
    let mut later_membrane = AthenaCausalMembrane::mount(successor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let later_conduct = later_membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    let later_conduct_changed_after_optical_return = later_conduct != resident_return;
    let successor = later_membrane.into_rest();
    if successor.identity() != successor_rest_identity_sha256
        || !same_body_identity_changed_after_optical_return
        || !production_morphology_preserved_after_optical_return
        || !later_conduct_changed_after_optical_return
        || !complete_generated_optical_source_crossed
    {
        return Err(
            "the physical optical return did not cultivate the same Athena body".to_owned(),
        );
    }
    fs::write(
        output.join("athena-optical-world-cultivated.rest"),
        &successor_wire,
    )
    .map_err(display)?;
    let witness = Sens5CultivatedReturnWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_rest_identity_sha256,
        successor_rest_identity_sha256,
        successor_body_identity_sha256,
        successor_wire_sha256: sha256(&successor_wire),
        production_morphology_identity_sha256,
        returned_png_sha256: primary.png_sha256.clone(),
        returned_hierarchy_identity_sha256,
        resident_receiver_current: injected,
        resident_return_before_cultivation: resident_return,
        cultivation,
        complete_generated_optical_source_crossed,
        same_body_identity_changed_after_optical_return,
        production_morphology_preserved_after_optical_return,
        later_conduct_changed_after_optical_return,
    };
    write_json(
        &output.join("29-cultivated-optical-return-witness.json"),
        &witness,
    )?;
    eprintln!("sens5 return: generated image changed the same Athena body and its later conduct");
    Ok(())
}

fn verify_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let foundation: Sens5FoundationWitness = serde_json::from_slice(
        &fs::read(output.join("09-foundation-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let cultivated: Sens5CultivatedReturnWitness = serde_json::from_slice(
        &fs::read(output.join("29-cultivated-optical-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let successor_wire =
        fs::read(output.join("athena-optical-world-cultivated.rest")).map_err(display)?;
    let successor = OpticalAthenaRest::read(&successor_wire).map_err(display)?;
    let successor_remounted_exactly = successor.identity()
        == cultivated.successor_rest_identity_sha256
        && sha256(&successor_wire) == cultivated.successor_wire_sha256;
    let primary = NativeAcousticRadiationInput::read(
        &fs::read(output.join("01-primary-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held_out = NativeAcousticRadiationInput::read(
        &fs::read(output.join("02-held-out-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let primary_field = successor.radiate(&primary).map_err(display)?;
    let held_out_field = successor.radiate(&held_out).map_err(display)?;
    let (primary_png, _) = primary_field
        .render_png(NativeOpticalReceiverIntervention::None)
        .map_err(display)?;
    let (held_out_png, _) = held_out_field
        .render_png(NativeOpticalReceiverIntervention::None)
        .map_err(display)?;
    let primary_field_reproduced_after_world_return =
        primary_field.identity_sha256 == foundation.primary_field_identity_sha256;
    let held_out_field_reproduced_after_world_return =
        held_out_field.identity_sha256 == foundation.held_out_field_identity_sha256;
    let primary_image_reproduced_after_world_return =
        sha256(&primary_png) == foundation.primary_png_sha256;
    let held_out_image_reproduced_after_world_return =
        sha256(&held_out_png) == foundation.held_out_png_sha256;
    let primary_and_held_out_remain_distinct =
        primary_field != held_out_field && primary_png != held_out_png;
    let successor_identity = successor.identity().to_owned();
    let optical_morphology = successor.production().identity_sha256.clone();
    let (acoustic, withdrawn_optical, _withdrawal): (_, _, NativeOpticalStandingMutation) =
        successor.withdraw_production().map_err(display)?;
    let targeted_optical_withdrawal_removed_owner =
        acoustic.identity() == cultivated.successor_body_identity_sha256;
    let acoustic_identity = acoustic.identity().to_owned();
    let (underlying, withdrawn_acoustic, _) = acoustic.withdraw_production().map_err(display)?;
    let (acoustic, _) =
        AcousticAthenaRest::restore_production(underlying, withdrawn_acoustic).map_err(display)?;
    let unrelated_acoustic_withdrawal_restored_exactly = acoustic.identity() == acoustic_identity;
    let (restored, _) =
        OpticalAthenaRest::restore_production(acoustic, withdrawn_optical).map_err(display)?;
    let targeted_optical_restoration_exact = restored.identity() == successor_identity;
    let restored_primary = restored.radiate(&primary).map_err(display)?;
    let unrelated_acoustic_sibling_did_not_change_optical_conduct = restored_primary
        == primary_field
        && restored.production().identity_sha256 == optical_morphology;
    let generated_source_image_absent_from_rested_morphology =
        !restored.production().source_image_retained
            && !restored.production().pixel_template_retained;
    let witness = Sens5VerificationWitness {
        successor_remounted_exactly,
        primary_field_reproduced_after_world_return,
        held_out_field_reproduced_after_world_return,
        primary_image_reproduced_after_world_return,
        held_out_image_reproduced_after_world_return,
        primary_and_held_out_remain_distinct,
        targeted_optical_withdrawal_removed_owner,
        targeted_optical_restoration_exact,
        unrelated_acoustic_withdrawal_restored_exactly,
        unrelated_acoustic_sibling_did_not_change_optical_conduct,
        generated_source_image_absent_from_rested_morphology,
    };
    if !witness.successor_remounted_exactly
        || !witness.primary_field_reproduced_after_world_return
        || !witness.held_out_field_reproduced_after_world_return
        || !witness.primary_image_reproduced_after_world_return
        || !witness.held_out_image_reproduced_after_world_return
        || !witness.primary_and_held_out_remain_distinct
        || !witness.targeted_optical_withdrawal_removed_owner
        || !witness.targeted_optical_restoration_exact
        || !witness.unrelated_acoustic_withdrawal_restored_exactly
        || !witness.unrelated_acoustic_sibling_did_not_change_optical_conduct
        || !witness.generated_source_image_absent_from_rested_morphology
    {
        return Err("the SENS5 source-detached rest or exact organ inverses failed".to_owned());
    }
    write_json(
        &output.join("30-source-detached-verification.json"),
        &witness,
    )?;
    eprintln!(
        "sens5 verify: remount, targeted optical inverse, and acoustic sibling invariance passed"
    );
    Ok(())
}

fn grade_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let foundation: Sens5FoundationWitness = serde_json::from_slice(
        &fs::read(output.join("09-foundation-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let interventions: Sens5InterventionWitness = serde_json::from_slice(
        &fs::read(output.join("14-intervention-projections.json")).map_err(display)?,
    )
    .map_err(display)?;
    let optical_return: Sens5OpticalReturnWitness = serde_json::from_slice(
        &fs::read(output.join("27-optical-world-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let cultivated: Sens5CultivatedReturnWitness = serde_json::from_slice(
        &fs::read(output.join("29-cultivated-optical-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let verified: Sens5VerificationWitness = serde_json::from_slice(
        &fs::read(output.join("30-source-detached-verification.json")).map_err(display)?,
    )
    .map_err(display)?;
    let result = Sens5Return {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        predecessor_rest_identity_sha256: foundation.predecessor_rest_identity_sha256,
        optical_foundation_identity_sha256: foundation.optical_rest_identity_sha256,
        cultivated_successor_identity_sha256: cultivated.successor_rest_identity_sha256,
        native_cell_population: foundation.native_cell_population,
        native_cover_population: foundation.native_cover_population,
        alternative_cover_population: foundation.alternative_cover_population,
        richer_receiver_reopening_population: foundation.richer_receiver_reopening_population,
        distinct_native_fields_before_rendering: foundation.distinct_fields_before_rendering,
        distinct_images_after_rendering: foundation.distinct_images_after_rendering,
        crop_scale_color_chart_and_occlusion_returned: interventions.projections.len() == 4
            && optical_return.returns.len() == 6,
        all_intervention_differences_attributable: optical_return.intervention_returns_attributable,
        held_out_not_copied_from_cultivation: foundation.held_out_section_absent_from_cultivation
            && foundation.source_current_absent_from_morphology
            && foundation.source_image_absent_from_morphology
            && foundation.pixel_template_absent,
        source_detached_remount_reproduced_production: verified.successor_remounted_exactly
            && verified.primary_field_reproduced_after_world_return
            && verified.held_out_field_reproduced_after_world_return
            && verified.primary_image_reproduced_after_world_return
            && verified.held_out_image_reproduced_after_world_return,
        targeted_optical_ablation_removed_owner: verified.targeted_optical_withdrawal_removed_owner,
        targeted_optical_restoration_exact: verified.targeted_optical_restoration_exact,
        unrelated_acoustic_sibling_invariant: verified
            .unrelated_acoustic_withdrawal_restored_exactly
            && verified.unrelated_acoustic_sibling_did_not_change_optical_conduct,
        physical_optical_return_changed_same_body_identity: cultivated
            .same_body_identity_changed_after_optical_return,
        physical_optical_return_changed_later_conduct: cultivated
            .later_conduct_changed_after_optical_return,
        external_image_generator_called: false,
        stored_image_or_pixel_template_applied: !verified
            .generated_source_image_absent_from_rested_morphology,
        label_route_applied: !foundation.label_route_absent,
        cpu_semantic_replay_after_device: cultivated
            .resident_return_before_cultivation
            .cpu_semantic_replay_after_device,
        output_files: vec![
            "03-primary-native-optical-field.json".to_owned(),
            "04-held-out-native-optical-field.json".to_owned(),
            "07-primary-native-optical.png".to_owned(),
            "08-held-out-native-optical.png".to_owned(),
            "10-crop.png".to_owned(),
            "11-scale.png".to_owned(),
            "12-color-chart.png".to_owned(),
            "13-occlusion.png".to_owned(),
            "athena-optical-production.rest".to_owned(),
            "athena-optical-world-cultivated.rest".to_owned(),
        ],
    };
    if !result.distinct_native_fields_before_rendering
        || !result.distinct_images_after_rendering
        || !result.crop_scale_color_chart_and_occlusion_returned
        || !result.all_intervention_differences_attributable
        || !result.held_out_not_copied_from_cultivation
        || !result.source_detached_remount_reproduced_production
        || !result.targeted_optical_ablation_removed_owner
        || !result.targeted_optical_restoration_exact
        || !result.unrelated_acoustic_sibling_invariant
        || !result.physical_optical_return_changed_same_body_identity
        || !result.physical_optical_return_changed_later_conduct
        || result.external_image_generator_called
        || result.stored_image_or_pixel_template_applied
        || result.label_route_applied
        || result.cpu_semantic_replay_after_device
    {
        return Err("the SENS5 qualitative receiver did not close".to_owned());
    }
    write_json(&output.join("00-sens5-return.json"), &result)?;
    Ok(())
}

fn recover_hierarchy(
    card: &mut CudaRefineExecutor,
    name: &str,
    encoded: &[u8],
) -> Result<(OpticalPassage, HierarchicalOpticalPassage), String> {
    let visible = ImageReader::new(std::io::Cursor::new(encoded))
        .with_guessed_format()
        .map_err(display)?
        .decode()
        .map_err(display)?
        .to_rgb8();
    let exact = ExactRaster::new(
        ImageExtent {
            width: visible.width(),
            height: visible.height(),
        },
        visible
            .pixels()
            .map(|pixel| ExactRgb {
                red: pixel[0],
                green: pixel[1],
                blue: pixel[2],
            })
            .collect(),
    )
    .map_err(display)?;
    let background = exact
        .sample(0, 0)
        .ok_or("generated optical raster is empty")?;
    let raw = recover_optical_passage(
        card,
        format!("sens5/generated-optical/{name}/{}", sha256(encoded)),
        format!("memory://sens5/{name}"),
        encoded,
        &exact,
        background,
    )
    .map_err(display)?;
    let (hierarchy, device) =
        grow_optical_holons(card, &raw, OpticalHolonIntervention::None).map_err(display)?;
    if raw.components.is_empty()
        || raw.device.launches == 0
        || raw.device.cpu_semantic_fallback
        || hierarchy.holons.is_empty()
        || device.launches == 0
        || device.cpu_semantic_fallback
    {
        return Err(format!(
            "{name} did not return a resident multi-scale optical consequence: components={} relations={} raw-launches={} raw-cpu={} holons={} covers={} hierarchy-launches={} hierarchy-cpu={}",
            raw.components.len(),
            raw.relations.len(),
            raw.device.launches,
            raw.device.cpu_semantic_fallback,
            hierarchy.holons.len(),
            hierarchy.alternative_covers.len(),
            device.launches,
            device.cpu_semantic_fallback,
        ));
    }
    Ok((raw, hierarchy))
}

fn optical_receiver_current(
    raw: &OpticalPassage,
    hierarchy: &HierarchicalOpticalPassage,
) -> Result<ExactComplexWaveCurrent, String> {
    let real = BigInt::from(raw.components.len()) - BigInt::from(raw.ambiguity_fibres.len());
    let imaginary =
        BigInt::from(raw.relations.len()) + BigInt::from(hierarchy.alternative_covers.len());
    let current =
        ExactComplexWaveCurrent::new(Rat::from_integer(real), Rat::from_integer(imaginary));
    if current.is_zero() {
        return Err("the physical optical receiver current vanished".to_owned());
    }
    Ok(current)
}

fn continuing_native_address(
    rest: &impl AthenaMembraneStanding,
) -> Result<(life::athena_native::NativeSectionAddress, ReceiverId), String> {
    for address in &rest.membrane_realization().sections {
        let addressed = rest
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
    Err("the optical Athena body has no continuing native address".to_owned())
}

fn receiver_cells(
    cells: &[life::athena_native::LaboratoryCellAffineSection],
) -> Result<(String, String), String> {
    let left = cells.first().ok_or("the affine organ has no cells")?;
    let support = left
        .landmark_factors
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let shared = cells
        .iter()
        .skip(1)
        .find(|cell| {
            cell.landmark_factors
                .iter()
                .any(|factor| support.contains(factor))
        })
        .ok_or("the affine organ has no shared-support cell")?;
    Ok((left.cell_address.clone(), shared.cell_address.clone()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut here = env::current_dir().map_err(display)?;
    loop {
        if here.join("Cargo.toml").is_file() && here.join("blueprint/THE_ROADMAP.md").is_file() {
            return Ok(here);
        }
        if !here.pop() {
            return Err("workspace root not found".to_owned());
        }
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
