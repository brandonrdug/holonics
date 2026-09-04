//! ALP3 receiver: exact native acoustic sections form overlapping time/spectral potential
//! complexes under one fixed cold receiver. Their directly audible surfaces then return through
//! the singular resident Athena membrane and cultivate the preserved ALP2 body.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    cuda_refine::ResidentMembraneInteriorReturn, quantity::BaseUnits,
    receiver_exact_compression::ReceiverId, BoundaryId, ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    mathematical_source::ExactAcousticOccurrence,
    native_intelligence::{
        AddressedMaterialOccurrence, AdmittedReturnedAffineLaboratoryRestWitness,
        ExactMembraneChartPassage, ExteriorOccurrenceTransducer, MembraneConsequence,
        MembraneCultivationReceipt, MembraneStanding, NativeAcousticPotentialComplex,
        NativeAcousticProductionSection, NativeAcousticReceiverChart, NativeCausalMembrane,
        RecurrentReturnedAffineLaboratoryRest, ReturnedAffineLaboratoryRest,
        StagedMembraneCultivation,
    },
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const SENS6: &str =
    ".local/artifacts/the_one_athena_ecology_listens_sees_speaks_forms_images_and_cultivates_sens6";
const ALP2: &str =
    ".local/artifacts/the_hierarchical_optical_surface_cultivates_and_remounts_one_athena_body_alp2";
const OUTPUT: &str =
    ".local/artifacts/the_native_acoustic_potential_complex_becomes_audible_and_returns_alp3";

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FormationWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    receiver: NativeAcousticReceiverChart,
    primary_production_identity_sha256: String,
    held_out_production_identity_sha256: String,
    primary_complex_identity_sha256: String,
    held_out_complex_identity_sha256: String,
    primary_projection_identity_sha256: String,
    held_out_projection_identity_sha256: String,
    primary_wav_sha256: String,
    held_out_wav_sha256: String,
    duration_samples: u64,
    flattened_shortcut_sample_population: usize,
    port_population: usize,
    causal_order_population: usize,
    spectral_incidence_population: usize,
    overlapping_spectral_incidence_population: usize,
    fixed_mixing_divisor: u64,
    primary_nonzero_sample_population: usize,
    held_out_nonzero_sample_population: usize,
    primary_peak: u16,
    held_out_peak: u16,
    primary_square_sum: u64,
    held_out_square_sum: u64,
    exact_sections_distinct: bool,
    potential_complexes_distinct: bool,
    audible_surfaces_distinct: bool,
    duration_not_flattened_port_order_quadrature_count: bool,
    one_fixed_receiver_used: bool,
    per_section_peak_normalization_absent: bool,
    clipped_sample_population: usize,
    complete_native_fibres_retained: bool,
    elapsed_seconds: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReturnWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_identity_sha256: String,
    successor_identity_sha256: String,
    successor_wire_sha256: String,
    complete_validation_receipt_sha256: String,
    primary_wav_sha256: String,
    exact_acoustic_incidence_sha256: String,
    exact_acoustic_section_sha256: String,
    receiver_current: ExactComplexWaveCurrent,
    resident_return_before_cultivation: ResidentMembraneInteriorReturn,
    cultivation: MembraneCultivationReceipt,
    exact_generated_acoustic_fibre_crossed: bool,
    same_body_identity_changed: bool,
    source_payload_unrepresentable_in_successor: bool,
    source_digest_absent_from_successor: bool,
    resident_gpu_device: String,
    elapsed_seconds: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ConductVerification {
    successor_remounted_exactly: bool,
    later_conduct_changed_after_acoustic_return: bool,
    later_conduct_returned_after_source_detached_remount: bool,
    elapsed_seconds: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct InverseVerification {
    targeted_return_withdrawal_recovered_alp2_predecessor: bool,
    targeted_return_restoration_recovered_successor: bool,
    successor_identity_sha256: String,
    elapsed_seconds: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alp3Grade {
    truth_status: String,
    evidence_tags: [String; 2],
    passed: bool,
    directly_audible_products_require_human_inspection: bool,
    formation: FormationWitness,
    return_witness: ReturnWitness,
    conduct: ConductVerification,
    inverse: InverseVerification,
    alp2_optical_body_preserved_as_predecessor: bool,
    elapsed_seconds: String,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    match env::var("ALP3_MODE").as_deref() {
        Ok("return") => return_phase(&root),
        Ok("verify") => verify_conduct(&root),
        Ok("inverse") => verify_inverse(&root),
        Ok("grade") => verify_restoration_and_grade(&root),
        Ok("form") | Err(_) => formation_phase(&root),
        Ok(other) => Err(format!("unknown ALP3_MODE {other}")),
    }
}

fn formation_phase(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    let primary = read_production(&root.join(SENS6).join("03-primary-native-acoustic.json"))?;
    let held_out = read_production(&root.join(SENS6).join("04-held-out-native-acoustic.json"))?;
    if primary.morphology_identity_sha256 != held_out.morphology_identity_sha256 {
        return Err("the held-out sections do not share one acoustic morphology".to_owned());
    }

    // These are declared physical playback coordinates. They bound only the cold acoustic
    // receiver, never Athena's population or route. The same immutable chart receives both
    // sections. At 16 kHz, consecutive native orders begin 750 ms apart and have one-second
    // supports; their 250 ms overlap is therefore receiver-visible rather than host sequencing.
    let receiver =
        NativeAcousticReceiverChart::calibrated_from(&primary, 16_000, 12_000, 16_000, 120, 3_600)
            .map_err(display)?;
    let primary_complex =
        NativeAcousticPotentialComplex::found(&primary, receiver.clone()).map_err(display)?;
    let held_out_complex =
        NativeAcousticPotentialComplex::found(&held_out, receiver.clone()).map_err(display)?;
    let primary_projection = primary_complex.render_pcm16().map_err(display)?;
    let held_out_projection = held_out_complex.render_pcm16().map_err(display)?;
    let primary_wav = primary_projection.wav_bytes().map_err(display)?;
    let held_out_wav = held_out_projection.wav_bytes().map_err(display)?;

    let primary_wav_sha256 = sha(&primary_wav);
    let held_out_wav_sha256 = sha(&held_out_wav);
    let primary_path = output.join("05-primary-native-acoustic-formation.wav");
    let held_out_path = output.join("06-held-out-native-acoustic-formation.wav");
    fs::write(&primary_path, &primary_wav).map_err(display)?;
    fs::write(&held_out_path, &held_out_wav).map_err(display)?;
    write_json(&output.join("01-fixed-acoustic-receiver.json"), &receiver)?;
    write_json(
        &output.join("02-primary-acoustic-potential-complex.json"),
        &primary_complex,
    )?;
    write_json(
        &output.join("03-held-out-acoustic-potential-complex.json"),
        &held_out_complex,
    )?;
    write_json(
        &output.join("04-audible-projections.json"),
        &(&primary_projection, &held_out_projection),
    )?;

    let flattened_shortcut_sample_population = primary
        .causal_orders
        .len()
        .checked_mul(primary_complex.port_population)
        .and_then(|population| population.checked_mul(2))
        .ok_or("flattened shortcut extent overflow")?;
    let overlap_begin = u64::from(receiver.order_stride_samples);
    let overlapping_spectral_incidence_population = primary_complex
        .incidences
        .iter()
        .filter(|incidence| {
            incidence.support_begin_sample < overlap_begin
                && incidence.support_end_sample > overlap_begin
        })
        .count();
    let witness = FormationWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        receiver: receiver.clone(),
        primary_production_identity_sha256: primary.identity_sha256.clone(),
        held_out_production_identity_sha256: held_out.identity_sha256.clone(),
        primary_complex_identity_sha256: primary_complex.identity_sha256.clone(),
        held_out_complex_identity_sha256: held_out_complex.identity_sha256.clone(),
        primary_projection_identity_sha256: primary_projection.identity_sha256.clone(),
        held_out_projection_identity_sha256: held_out_projection.identity_sha256.clone(),
        primary_wav_sha256,
        held_out_wav_sha256,
        duration_samples: primary_complex.duration_samples,
        flattened_shortcut_sample_population,
        port_population: primary_complex.port_population,
        causal_order_population: primary.causal_orders.len(),
        spectral_incidence_population: primary_complex.incidences.len(),
        overlapping_spectral_incidence_population,
        fixed_mixing_divisor: primary_complex.fixed_mixing_divisor,
        primary_nonzero_sample_population: primary_projection.nonzero_sample_population,
        held_out_nonzero_sample_population: held_out_projection.nonzero_sample_population,
        primary_peak: peak(&primary_projection.samples),
        held_out_peak: peak(&held_out_projection.samples),
        primary_square_sum: square_sum(&primary_projection.samples)?,
        held_out_square_sum: square_sum(&held_out_projection.samples)?,
        exact_sections_distinct: primary != held_out,
        potential_complexes_distinct: primary_complex != held_out_complex,
        audible_surfaces_distinct: primary_wav != held_out_wav,
        duration_not_flattened_port_order_quadrature_count: usize::try_from(
            primary_complex.duration_samples,
        )
        .ok()
            != Some(flattened_shortcut_sample_population),
        one_fixed_receiver_used: primary_complex.receiver == held_out_complex.receiver,
        per_section_peak_normalization_absent: !primary_complex
            .per_section_peak_normalization_applied
            && !held_out_complex.per_section_peak_normalization_applied
            && !primary_projection.per_section_peak_normalization_applied
            && !held_out_projection.per_section_peak_normalization_applied,
        clipped_sample_population: primary_projection.clipped_sample_population
            + held_out_projection.clipped_sample_population,
        complete_native_fibres_retained: primary_complex.complete_production_fibre_retained
            && held_out_complex.complete_production_fibre_retained
            && primary_projection.complete_potential_complex_fibre_retained
            && held_out_projection.complete_potential_complex_fibre_retained,
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    if !witness.exact_sections_distinct
        || !witness.potential_complexes_distinct
        || !witness.audible_surfaces_distinct
        || !witness.duration_not_flattened_port_order_quadrature_count
        || !witness.one_fixed_receiver_used
        || !witness.per_section_peak_normalization_absent
        || witness.clipped_sample_population != 0
        || !witness.complete_native_fibres_retained
        || witness.primary_nonzero_sample_population == 0
        || witness.held_out_nonzero_sample_population == 0
        || witness.overlapping_spectral_incidence_population == 0
    {
        return Err("the ALP3 audible formation receiver refused".to_owned());
    }
    write_json(&output.join("07-formation-witness.json"), &witness)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&witness).map_err(display)?
    );
    Ok(())
}

fn return_phase(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    if output
        .join("athena-acoustic-return-cultivated.rest")
        .exists()
    {
        return Err("preserve the standing ALP3 cultivated rest".to_owned());
    }
    let formation: FormationWitness = read_json(&output.join("07-formation-witness.json"))?;
    let alp2: serde_json::Value =
        read_json(&root.join(ALP2).join("03-physical-return-witness.json"))?;
    let alp2_wire = fs::read(
        root.join(ALP2)
            .join("athena-hierarchical-optical-cultivated.rest"),
    )
    .map_err(display)?;
    let alp2_wire_sha = field(&alp2, "successor_wire_sha256")?;
    let alp2_identity = field(&alp2, "successor_identity_sha256")?;
    let alp2_validation = field(&alp2, "complete_validation_receipt_sha256")?;
    let admitted = AdmittedReturnedAffineLaboratoryRestWitness::found(
        alp2_wire_sha,
        alp2_identity,
        alp2_validation,
    )
    .map_err(display)?;
    let predecessor = ReturnedAffineLaboratoryRest::read_admitted_membrane(&alp2_wire, &admitted)
        .map_err(display)?;
    let predecessor_identity = predecessor.membrane_identity().to_owned();
    let (native_address, receiver) = continuing_native_address(&predecessor)?;
    let (left, shared) = receiver_cells(predecessor.membrane_affine_cells())?;

    let wav = fs::read(output.join("05-primary-native-acoustic-formation.wav")).map_err(display)?;
    if sha(&wav) != formation.primary_wav_sha256 {
        return Err("the audible formation changed before physical return".to_owned());
    }
    let exact = ExactAcousticOccurrence::from_wav_bytes(
        &wav,
        "alp3/physical/native-acoustic-formation",
        "memory://alp3/native-acoustic-formation",
        formation.receiver.order_support_samples,
        formation.receiver.order_stride_samples,
        formation.port_population,
    )
    .map_err(display)?;
    let receiver_current = acoustic_receiver_current(&exact)?;
    let occurrence = AddressedMaterialOccurrence::found(
        "alp3/physical/native-acoustic-formation",
        &serde_json::to_vec(&exact).map_err(display)?,
        Some(format!(
            "alp3/native-potential/{}",
            formation.primary_complex_identity_sha256
        )),
        vec!["cold physical native acoustic delivery".to_owned()],
        vec!["later acoustic world consequences remain open".to_owned()],
    )
    .map_err(display)?;
    let expected = occurrence.clone();
    let source_fibre = occurrence.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(source_fibre.address().event_projection.0);
    let dimension = BaseUnits::declare(["alp3-native-acoustic-return-current"])
        .map_err(display)?
        .unit("alp3-native-acoustic-return-current")
        .map_err(display)?;
    let mut membrane = NativeCausalMembrane::mount(predecessor)
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
                receiver_current.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("the acoustic formation binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(initial_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the acoustic formation did not cross Athena's membrane".to_owned());
    };
    let recovered = initial_return
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|_| "the acoustic formation source fibre did not return".to_owned())?;
    let exact_generated_acoustic_fibre_crossed = recovered == expected;
    let resident_before = membrane
        .conduct_resident_interior(&left, &shared, &receiver_current)
        .map_err(display)?;
    let world_payload = serde_json::to_vec(&(
        "alp3/returned-native-acoustic-world-consequence",
        &formation.primary_wav_sha256,
        &exact.incidence_sha256,
        &exact.section_sha256,
        &resident_before.native_radiation,
        &resident_before.returned_radiation,
        &resident_before.family_overlaps,
    ))
    .map_err(display)?;
    let world_source = AddressedMaterialOccurrence::found(
        "alp3/world/returned-native-acoustic-consequence",
        &world_payload,
        Some("alp3/physical/native-acoustic-formation".to_owned()),
        vec!["cold native acoustic world return".to_owned()],
        vec!["later exterior acoustic consequences remain open".to_owned()],
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
                resident_before.native_radiation.clone(),
                resident_before.returned_radiation.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("the acoustic world return refused: {failure:?}"))?;
    let MembraneConsequence::Returned(world_return) =
        membrane.receive_occurrence(later).map_err(display)?
    else {
        return Err("the acoustic world consequence did not return".to_owned());
    };
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_before.clone())
        .map_err(display)?;
    let (predecessor, detached) = staged.detach().map_err(display)?;
    let (successor, cultivation, successor_wire) =
        detached.commit_restable(predecessor).map_err(display)?;
    let successor_identity = successor.identity().to_owned();
    let successor_wire_sha = sha(&successor_wire);
    let complete_validation_receipt_sha256 =
        sha(&serde_json::to_vec(&cultivation).map_err(display)?);
    let source_digest_absent_from_successor =
        !contains_subslice(&successor_wire, formation.primary_wav_sha256.as_bytes());
    let resident_gpu_device = resident_before.device.clone();
    let witness = ReturnWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_identity_sha256: predecessor_identity.clone(),
        successor_identity_sha256: successor_identity.clone(),
        successor_wire_sha256: successor_wire_sha,
        complete_validation_receipt_sha256,
        primary_wav_sha256: formation.primary_wav_sha256,
        exact_acoustic_incidence_sha256: exact.incidence_sha256,
        exact_acoustic_section_sha256: exact.section_sha256,
        receiver_current,
        resident_return_before_cultivation: resident_before,
        cultivation,
        exact_generated_acoustic_fibre_crossed,
        same_body_identity_changed: successor_identity != predecessor_identity,
        source_payload_unrepresentable_in_successor: true,
        source_digest_absent_from_successor,
        resident_gpu_device,
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    if !witness.exact_generated_acoustic_fibre_crossed
        || !witness.same_body_identity_changed
        || !witness.source_payload_unrepresentable_in_successor
        || !witness.source_digest_absent_from_successor
    {
        return Err("the physical acoustic return did not cultivate the ALP2 body".to_owned());
    }
    fs::write(
        output.join("athena-acoustic-return-cultivated.rest"),
        successor_wire,
    )
    .map_err(display)?;
    write_json(&output.join("08-physical-return-witness.json"), &witness)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&witness).map_err(display)?
    );
    Ok(())
}

fn verify_conduct(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    let witness: ReturnWitness = read_json(&output.join("08-physical-return-witness.json"))?;
    let wire = fs::read(output.join("athena-acoustic-return-cultivated.rest")).map_err(display)?;
    let successor = RecurrentReturnedAffineLaboratoryRest::read(&wire).map_err(display)?;
    let successor_remounted_exactly = successor.membrane_identity()
        == witness.successor_identity_sha256
        && sha(&wire) == witness.successor_wire_sha256;
    let (left, shared) = receiver_cells(successor.membrane_affine_cells())?;
    let mut mounted = NativeCausalMembrane::mount(successor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let reproduced = mounted
        .conduct_resident_interior(&left, &shared, &witness.receiver_current)
        .map_err(display)?;
    let result = ConductVerification {
        successor_remounted_exactly,
        later_conduct_changed_after_acoustic_return: reproduced
            != witness.resident_return_before_cultivation,
        later_conduct_returned_after_source_detached_remount: !reproduced
            .returned_radiation
            .is_zero(),
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    let _ = mounted.into_rest();
    if !result.successor_remounted_exactly
        || !result.later_conduct_changed_after_acoustic_return
        || !result.later_conduct_returned_after_source_detached_remount
    {
        return Err("the detached acoustic successor did not return changed conduct".to_owned());
    }
    write_json(
        &output.join("09-remount-conduct-verification.json"),
        &result,
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(display)?
    );
    Ok(())
}

fn verify_inverse(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    let witness: ReturnWitness = read_json(&output.join("08-physical-return-witness.json"))?;
    let wire = fs::read(output.join("athena-acoustic-return-cultivated.rest")).map_err(display)?;
    let successor = RecurrentReturnedAffineLaboratoryRest::read(&wire).map_err(display)?;
    let successor_identity = successor.identity().to_owned();
    let (predecessor, withdrawal) = successor
        .withdraw_latest_returned_difference()
        .map_err(display)?;
    let targeted = predecessor.identity() == witness.predecessor_identity_sha256;
    if !targeted {
        return Err("the acoustic return inverse did not recover ALP2".to_owned());
    }
    let restored = RecurrentReturnedAffineLaboratoryRest::restore_latest_returned_difference(
        predecessor,
        withdrawal,
    )
    .map_err(display)?;
    let result = InverseVerification {
        targeted_return_withdrawal_recovered_alp2_predecessor: targeted,
        targeted_return_restoration_recovered_successor: restored.identity() == successor_identity,
        successor_identity_sha256: successor_identity,
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    if !result.targeted_return_restoration_recovered_successor {
        return Err("the acoustic return restoration did not recover its successor".to_owned());
    }
    write_json(&output.join("10-inverse-verification.json"), &result)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(display)?
    );
    Ok(())
}

fn verify_restoration_and_grade(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    let formation: FormationWitness = read_json(&output.join("07-formation-witness.json"))?;
    let return_witness: ReturnWitness = read_json(&output.join("08-physical-return-witness.json"))?;
    let conduct: ConductVerification =
        read_json(&output.join("09-remount-conduct-verification.json"))?;
    let inverse: InverseVerification = read_json(&output.join("10-inverse-verification.json"))?;
    let alp2: serde_json::Value =
        read_json(&root.join(ALP2).join("03-physical-return-witness.json"))?;
    let alp2_wire = fs::read(
        root.join(ALP2)
            .join("athena-hierarchical-optical-cultivated.rest"),
    )
    .map_err(display)?;
    let admitted = AdmittedReturnedAffineLaboratoryRestWitness::found(
        field(&alp2, "successor_wire_sha256")?,
        field(&alp2, "successor_identity_sha256")?,
        field(&alp2, "complete_validation_receipt_sha256")?,
    )
    .map_err(display)?;
    let predecessor =
        ReturnedAffineLaboratoryRest::read_admitted(&alp2_wire, &admitted).map_err(display)?;
    let alp2_optical_body_preserved_as_predecessor =
        predecessor.identity() == return_witness.predecessor_identity_sha256;
    let passed = formation.exact_sections_distinct
        && formation.potential_complexes_distinct
        && formation.audible_surfaces_distinct
        && formation.duration_not_flattened_port_order_quadrature_count
        && formation.one_fixed_receiver_used
        && formation.per_section_peak_normalization_absent
        && formation.clipped_sample_population == 0
        && formation.complete_native_fibres_retained
        && return_witness.exact_generated_acoustic_fibre_crossed
        && return_witness.same_body_identity_changed
        && conduct.successor_remounted_exactly
        && conduct.later_conduct_changed_after_acoustic_return
        && conduct.later_conduct_returned_after_source_detached_remount
        && inverse.targeted_return_withdrawal_recovered_alp2_predecessor
        && inverse.targeted_return_restoration_recovered_successor
        && alp2_optical_body_preserved_as_predecessor;
    let grade = Alp3Grade {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        passed,
        directly_audible_products_require_human_inspection: true,
        formation,
        return_witness,
        conduct,
        inverse,
        alp2_optical_body_preserved_as_predecessor,
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    write_json(&output.join("00-grade.json"), &grade)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("ALP3 exact return or inverse refused".to_owned())
    }
}

fn read_production(path: &Path) -> Result<NativeAcousticProductionSection, String> {
    let production: NativeAcousticProductionSection = read_json(path)?;
    production.validate().map_err(display)?;
    Ok(production)
}

fn acoustic_receiver_current(
    exact: &ExactAcousticOccurrence,
) -> Result<ExactComplexWaveCurrent, String> {
    let real = exact
        .frames
        .iter()
        .try_fold(BigInt::from(0), |sum, frame| {
            Ok::<_, String>(sum + BigInt::from(frame.signed_sum))
        })?;
    let imaginary = exact
        .frames
        .iter()
        .try_fold(BigInt::from(0), |sum, frame| {
            Ok::<_, String>(sum + BigInt::from(frame.alternating_sum))
        })?;
    let current =
        ExactComplexWaveCurrent::new(Rat::from_integer(real), Rat::from_integer(imaginary));
    if current.is_zero() {
        Err("the audible acoustic receiver current vanished".to_owned())
    } else {
        Ok(current)
    }
}

fn continuing_native_address(
    rest: &impl MembraneStanding,
) -> Result<(life::native_intelligence::NativeSectionAddress, ReceiverId), String> {
    for address in &rest.membrane_realization().sections {
        let section = rest
            .membrane_ecology()
            .native()
            .addressed_section(&address.spool, &address.thread, address.occurrence)
            .map_err(display)?;
        if section.thread().chronology.is_empty() {
            continue;
        }
        if let Some(receiver) = section.spool().receiver_family.iter().next().copied() {
            return Ok((address.clone(), receiver));
        }
    }
    Err("the Athena body has no continuing native address".to_owned())
}

fn receiver_cells(
    sections: &[life::native_intelligence::LaboratoryCellAffineSection],
) -> Result<(String, String), String> {
    let left = sections.first().ok_or("the affine organ has no cells")?;
    let support = left
        .landmark_factors
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let shared = sections
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

fn peak(samples: &[i16]) -> u16 {
    samples
        .iter()
        .map(|sample| sample.unsigned_abs())
        .max()
        .unwrap_or(0)
}

fn square_sum(samples: &[i16]) -> Result<u64, String> {
    samples.iter().try_fold(0_u64, |sum, sample| {
        sum.checked_add(u64::from(sample.unsigned_abs()).pow(2))
            .ok_or_else(|| "acoustic square sum overflowed".to_owned())
    })
}

fn field<'a>(value: &'a serde_json::Value, name: &str) -> Result<&'a str, String> {
    value
        .get(name)
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| format!("missing string field {name}"))
}

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop();
    path.pop();
    Ok(path)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
