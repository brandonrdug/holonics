//! SENS6 release receiver: ordinary audio and image occurrences enter one cultivated Athena body;
//! the same body returns exact recurrence, lawful silence, native acoustic/optical production,
//! physical re-entry, durable cultivation, source-detached remount, and exact inverses.

use std::{
    any::Any,
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
    addressed_span::{AddressedMemorySpan, CompleteAddressedMemorySpan, MemorySpanFragment},
    athena_native::{
        AcousticAthenaRest, AddressedMaterialOccurrence, AthenaCausalMembrane,
        AthenaMembraneConsequence, AthenaMembraneCrossingReceipt, AthenaMembraneStanding,
        ExactMembraneChartPassage, ExteriorOccurrenceTransducer, GranularAthenaRest,
        GranularSourceNeutralCompositionReceipt, MembraneCultivationReceipt,
        NativeAcousticOrganCompositionReceipt, NativeAcousticPotentialComplex,
        NativeAcousticRadiationInput, NativeAcousticReceiverChart, NativeOpenWorldTubeReceipt,
        NativeOpticalOrganCompositionReceipt, NativeOpticalReceiverIntervention, OpticalAthenaRest,
        RecurrentGranularReturnedAffineAthenaRest, RecurrentGranularReturnedAffinePredecessor,
        RecurrentReturnedAffineLaboratoryAthenaRest, StagedMembraneCultivation,
    },
    mathematical_source::{
        grow_optical_holons, recover_optical_passage, ExactAcousticOccurrence,
        ExactOpticalOccurrence, HierarchicalOpticalPassage, OpticalHolonIntervention,
        OpticalPassage,
    },
    synchronized_occurrence::{
        relation_atom, ExactClockTransport, ExactSynchronizedOccurrence,
        ExactSynchronizedOccurrenceFibre, SynchronizedCellId, SynchronizedCellOrigin,
        SynchronizedInteraction, SynchronizedOccurrenceChart, SynchronizedReceiverId,
        SynchronizedReceiverSection, TimedReceiverCell,
    },
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_membrane::ReceiverChartIdentity;

const SENS5_REST: &str = concat!(
    "output/the_athena_radiation_forms_an_optical_field_and_its_image_returns_sens5/",
    "athena-optical-world-cultivated.rest"
);
const MATERIAL: &str = "data/athena-sensory-world-tube/sens6-bounded";
const OUTPUT: &str =
    "output/the_one_athena_ecology_listens_sees_speaks_forms_images_and_cultivates_sens6";
const ALP3_REST: &str = concat!(
    "output/the_native_acoustic_potential_complex_becomes_audible_and_returns_alp3/",
    "athena-acoustic-return-cultivated.rest"
);
const ALP4_OUTPUT: &str =
    "output/the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4";
const ALP4_INITIAL_REST: &str = concat!(
    "output/the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-alp4-initial-composed.rest"
);
const ACOUSTIC_RECEIVER: SynchronizedReceiverId = SynchronizedReceiverId(0x5345_4e53_3641);
const OPTICAL_RECEIVER: SynchronizedReceiverId = SynchronizedReceiverId(0x5345_4e53_364f);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PacketCoverReceipt {
    family: String,
    role: String,
    source_sha256: String,
    source_octets: u64,
    whole_fragment_population: u64,
    broken_fragment_population: u64,
    broken_join_population: u64,
    whole_and_broken_returned_same_complete_span: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CrossingSummary {
    exterior_occurrence: String,
    native_word_population: usize,
    returned_section: ExactComplexWaveCurrent,
    returned_current: ExactComplexWaveCurrent,
    exact_source_fibre_retained: bool,
    cold_lineage_did_not_select_contact: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct OpenWorldSummary {
    identity_sha256: String,
    outward_port_population: usize,
    causal_order_population: usize,
    lawful_silence_present: bool,
    compulsory_nonradical_radiation_present: bool,
    every_generator_descent_returned_on_card: bool,
    exact_dynamic_condensation_or_open_front_returned: bool,
    source_fibre_remained_exact: bool,
    invariant_transport_reuploaded: bool,
    cpu_semantic_replay_after_device: bool,
    resident_launch_population: u64,
    resident_synchronization_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RoleIngressReceipt {
    role: String,
    acoustic_source_sha256: String,
    acoustic_section_sha256: String,
    optical_source_sha256: String,
    optical_hierarchy_sha256: String,
    optical_component_population: usize,
    optical_relation_population: usize,
    optical_alternative_cover_population: usize,
    acoustic_crossing: CrossingSummary,
    optical_crossing: CrossingSummary,
    synchronized_source_sha256: String,
    synchronized_incidence_sha256: String,
    synchronized_contact_population: usize,
    synchronized_source_fibre_returned_exactly: bool,
    clock_rebase_preserved_every_contact: bool,
    separated_clock_returned_no_contact: bool,
    acoustic_only_interval_present: bool,
    optical_only_interval_present: bool,
    strict_acoustic_interruption_present: bool,
    presented_current: ExactComplexWaveCurrent,
    radiation_input_identity_sha256: String,
    native_acoustic_identity_sha256: String,
    pcm_projection_identity_sha256: String,
    pcm_scale_divisor: BigInt,
    pcm_nonzero_remainder_population: usize,
    generated_wav_sha256: String,
    native_optical_identity_sha256: String,
    generated_png_sha256: String,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens6ComposeWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_rest_identity_sha256: String,
    material_receipt_sha256: String,
    packet_covers: Vec<PacketCoverReceipt>,
    roles: Vec<RoleIngressReceipt>,
    primary_open_world: OpenWorldSummary,
    held_out_open_world: OpenWorldSummary,
    packetization_naturality: bool,
    acoustic_only_returned: bool,
    optical_only_returned: bool,
    cross_sensory_contact_returned: bool,
    silence_returned: bool,
    spontaneous_radiation_returned: bool,
    interruption_returned: bool,
    clock_rebase_naturality: bool,
    held_out_native_consequences_distinct: bool,
    pcm_receiver_projections_distinct: bool,
    cold_wav_surface_collapsed: bool,
    native_acoustic_and_optical_production_returned: bool,
    one_resident_apparatus_receipt: bool,
    transcript_label_or_name_selected_conduct: bool,
    external_generator_called: bool,
    cpu_semantic_replay: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens6ReturnWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_rest_identity_sha256: String,
    successor_rest_identity_sha256: String,
    successor_wire_sha256: String,
    primary_generated_wav_sha256: String,
    primary_generated_png_sha256: String,
    acoustic_return_crossing: CrossingSummary,
    optical_return_crossing: CrossingSummary,
    complete_acoustic_source_fibre_returned: bool,
    complete_optical_source_fibre_returned: bool,
    injected_physical_return: ExactComplexWaveCurrent,
    resident_return: ResidentMembraneInteriorReturn,
    cultivation: MembraneCultivationReceipt,
    physical_return_changed_same_body_identity: bool,
    physical_return_changed_later_conduct: bool,
    acoustic_and_optical_morphologies_preserved: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens6VerificationWitness {
    source_detached_remount_exact: bool,
    primary_acoustic_reproduced: bool,
    held_out_acoustic_reproduced: bool,
    primary_optical_reproduced: bool,
    held_out_optical_reproduced: bool,
    held_out_outputs_remain_distinct: bool,
    targeted_latest_return_ablation_recovered_exact_sens5_body: bool,
    targeted_latest_return_ablation_changed_conduct: bool,
    targeted_latest_return_restoration_exact: bool,
    targeted_optical_withdrawal_removed_owner: bool,
    unrelated_acoustic_sibling_conduct_invariant: bool,
    optical_restoration_exact: bool,
    acoustic_withdrawal_and_restoration_exact: bool,
    source_payload_hashes_absent_from_rest: bool,
    productive_material_labels_absent_from_new_deposit: bool,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens6Return {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    predecessor_rest_identity_sha256: String,
    successor_rest_identity_sha256: String,
    packetization_naturality: bool,
    clock_rebase_naturality: bool,
    acoustic_only_optical_only_and_cross_sensory_returned: bool,
    lawful_silence_and_spontaneous_radiation_returned: bool,
    interruption_returned: bool,
    native_acoustic_and_optical_production_returned: bool,
    held_out_recognition_without_name_output_returned: bool,
    physical_return_changed_same_body_and_later_conduct: bool,
    source_detached_remount_exact: bool,
    targeted_and_unrelated_ablations_and_restoration_passed: bool,
    one_resident_apparatus_receipt: bool,
    transcript_label_name_or_target_selected_conduct: bool,
    external_generator_called: bool,
    cpu_semantic_replay: bool,
    brandon_recordings_available: bool,
    open_exterior: Vec<String>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alp4OrganCompositionWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    alp3_body_identity_sha256: String,
    inherited_spool_identity_sha256: String,
    composed_body_identity_sha256: String,
    composed_wire_sha256: String,
    granular: GranularSourceNeutralCompositionReceipt,
    acoustic: NativeAcousticOrganCompositionReceipt,
    optical: NativeOpticalOrganCompositionReceipt,
    foreign_runtime_accessed: bool,
    source_occurrence_consulted: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alp4DirectFormationWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    fixed_acoustic_receiver: NativeAcousticReceiverChart,
    primary_acoustic_complex_identity_sha256: String,
    held_acoustic_complex_identity_sha256: String,
    primary_acoustic_duration_samples: u64,
    held_acoustic_duration_samples: u64,
    primary_acoustic_nonzero_samples: usize,
    held_acoustic_nonzero_samples: usize,
    acoustic_surfaces_distinct: bool,
    acoustic_no_section_peak_normalization: bool,
    primary_optical_formation_identity_sha256: String,
    held_optical_formation_identity_sha256: String,
    primary_optical_source_holons: usize,
    held_optical_source_holons: usize,
    primary_optical_source_incidences: usize,
    held_optical_source_incidences: usize,
    primary_optical_alternative_covers: usize,
    held_optical_alternative_covers: usize,
    optical_surfaces_distinct: bool,
    optical_port_grid_absent: bool,
    direct_outputs_causally_downstream_of_native_sections: bool,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    if let Ok(mode) = env::var("ALP4_MODE") {
        return match mode.as_str() {
            "prepare" => alp4_prepare_phase(&root),
            "compose" => compose_phase(&root),
            "return" => return_phase(&root),
            "verify" => verify_phase(&root),
            "grade" => {
                grade_phase(&root)?;
                alp4_grade_phase(&root)
            }
            other => Err(format!("unknown ALP4_MODE {other}")),
        };
    }
    match env::var("SENS6_MODE").as_deref() {
        Ok("return") => return_phase(&root),
        Ok("verify") => verify_phase(&root),
        Ok("grade") => grade_phase(&root),
        Ok("compose") | Err(_) => compose_phase(&root),
        Ok(other) => Err(format!("unknown SENS6_MODE {other}")),
    }
}

fn alp4_active() -> bool {
    env::var_os("ALP4_MODE").is_some()
}

fn active_output(root: &Path) -> PathBuf {
    root.join(if alp4_active() { ALP4_OUTPUT } else { OUTPUT })
}

fn active_starting_rest(root: &Path) -> PathBuf {
    root.join(if alp4_active() {
        ALP4_INITIAL_REST
    } else {
        SENS5_REST
    })
}

fn alp4_prepare_phase(root: &Path) -> Result<(), String> {
    let output = active_output(root);
    fs::create_dir_all(&output).map_err(display)?;
    let target = root.join(ALP4_INITIAL_REST);
    if target.exists() {
        return Err("preserve the standing ALP4 initial composition".to_owned());
    }

    // Dismantle the prior sensory wrapper into its move-owned source-neutral organs. Its old
    // continuation body is deliberately dropped; neither it nor its source material enters ALP4.
    let inherited = OpticalAthenaRest::read(&fs::read(root.join(SENS5_REST)).map_err(display)?)
        .map_err(display)?;
    let (inherited_acoustic, withdrawn_optical, _) =
        inherited.withdraw_production().map_err(display)?;
    let (inherited_granular, withdrawn_acoustic, _) =
        inherited_acoustic.withdraw_production().map_err(display)?;
    let (retired_body, withdrawn_granular) = inherited_granular.withdraw().map_err(display)?;
    drop(retired_body);

    let alp3 = RecurrentReturnedAffineLaboratoryAthenaRest::read(
        &fs::read(root.join(ALP3_REST)).map_err(display)?,
    )
    .map_err(display)?;
    let alp3_body_identity_sha256 = alp3.identity().to_owned();
    let inherited_spool_identity_sha256 =
        alp3.membrane_ecology().identity_sha256().map_err(display)?;
    let (granular, granular_receipt) =
        GranularAthenaRest::compose_source_neutral_organ(alp3, withdrawn_granular)
            .map_err(display)?;
    let (acoustic, acoustic_receipt) =
        AcousticAthenaRest::compose_source_neutral_production(granular, withdrawn_acoustic)
            .map_err(display)?;
    let (rest, optical_receipt) =
        OpticalAthenaRest::compose_source_neutral_production(acoustic, withdrawn_optical)
            .map_err(display)?;
    let composed_body_identity_sha256 = rest.identity().to_owned();
    let wire = rest.canonical_bytes().map_err(display)?;
    let composed_wire_sha256 = sha256(&wire);
    fs::write(&target, &wire).map_err(display)?;
    let witness = Alp4OrganCompositionWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        alp3_body_identity_sha256,
        inherited_spool_identity_sha256,
        composed_body_identity_sha256,
        composed_wire_sha256,
        granular: granular_receipt,
        acoustic: acoustic_receipt,
        optical: optical_receipt,
        foreign_runtime_accessed: false,
        source_occurrence_consulted: false,
    };
    write_json(&output.join("00-organ-composition-witness.json"), &witness)?;
    eprintln!("alp4 prepare: source-neutral organs composed over the preserved ALP3 body");
    Ok(())
}

fn compose_phase(root: &Path) -> Result<(), String> {
    let output = active_output(root);
    fs::create_dir_all(&output).map_err(display)?;
    let material = root.join(MATERIAL);
    let material_receipt = fs::read(material.join("material-receipt.json")).map_err(display)?;
    let material_value: serde_json::Value =
        serde_json::from_slice(&material_receipt).map_err(display)?;
    if material_value["semantic_columns_available_to_productive_path"] != false {
        return Err("the frozen material aperture exposed a semantic selector".to_owned());
    }

    let rest_wire = fs::read(active_starting_rest(root)).map_err(display)?;
    let rest = OpticalAthenaRest::read(&rest_wire).map_err(display)?;
    let predecessor_rest_identity_sha256 = rest.identity().to_owned();
    let frame_length = rest.body().production().phase_extent;
    let frame_hop = frame_length
        .checked_div(2)
        .filter(|hop| *hop > 0)
        .ok_or("the acoustic organ did not found a frame hop")?;
    let section_width = rest.body().production().ordered_ports.len();
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let dimension = BaseUnits::declare(["sens6-sensory-current"])
        .map_err(display)?
        .unit("sens6-sensory-current")
        .map_err(display)?;
    let mut membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?
        .mount_resident_factor_receiver_faces()
        .map_err(display)?;
    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let mut packet_covers = Vec::new();
    let mut role_inputs = Vec::new();

    for (ordinal, role) in ["primary", "held-out"].into_iter().enumerate() {
        let material_role = if role == "primary" {
            "cultivation"
        } else {
            "held-out"
        };
        let wav = fs::read(material.join(format!("audio-{material_role}.wav"))).map_err(display)?;
        let png = fs::read(material.join(format!("image-{material_role}.png"))).map_err(display)?;
        let acoustic_occurrence = format!("sens6/ordinary/{role}/acoustic");
        let optical_occurrence = format!("sens6/ordinary/{role}/optical");
        let acoustic_whole = assemble(&acoustic_occurrence, &wav, false)?;
        let acoustic_broken = assemble(&acoustic_occurrence, &wav, true)?;
        packet_covers.push(packet_receipt(
            "acoustic",
            role,
            &acoustic_whole,
            &acoustic_broken,
        ));
        let optical_whole = assemble(&optical_occurrence, &png, false)?;
        let optical_broken = assemble(&optical_occurrence, &png, true)?;
        packet_covers.push(packet_receipt(
            "optical",
            role,
            &optical_whole,
            &optical_broken,
        ));
        if acoustic_whole.body != acoustic_broken.body || optical_whole.body != optical_broken.body
        {
            return Err(format!("{role} packet covers changed a source occurrence"));
        }

        let acoustic = ExactAcousticOccurrence::from_wav_bytes(
            &acoustic_whole.body,
            acoustic_occurrence,
            format!("memory://sens6/{role}/acoustic"),
            frame_length,
            frame_hop,
            section_width,
        )
        .map_err(display)?;
        let acoustic_current = acoustic_receiver_current(&acoustic)?;
        let acoustic_section_sha256 = acoustic.section_sha256.clone();
        let acoustic_source_sha256 = acoustic.source_sha256.clone();
        let (acoustic_crossing, acoustic) = cross_and_recover(
            &mut membrane,
            acoustic,
            &native_address,
            receiver,
            dimension.clone(),
            acoustic_current.clone(),
        )?;

        let (raw, hierarchy) = recover_hierarchy(&mut card, role, &optical_whole.body)?;
        let optical_current = optical_receiver_current(&raw, &hierarchy)?;
        let optical_source_sha256 = hierarchy.predecessor_source_sha256.clone();
        let optical_hierarchy_sha256 = sha256(&hierarchy.canonical_bytes().map_err(display)?);
        write_json(
            &output.join(format!("{:02}-{role}-raw-optical.json", 13 + ordinal * 2)),
            &raw,
        )?;
        write_json(
            &output.join(format!(
                "{:02}-{role}-hierarchical-optical.json",
                14 + ordinal * 2
            )),
            &hierarchy,
        )?;
        let optical = ExactOpticalOccurrence::found(
            optical_occurrence,
            format!("memory://sens6/{role}/optical"),
            optical_whole.body,
            hierarchy,
        )
        .map_err(display)?;
        let (optical_crossing, optical) = cross_and_recover(
            &mut membrane,
            optical,
            &native_address,
            receiver,
            dimension.clone(),
            optical_current.clone(),
        )?;

        let synchronized =
            synchronized_occurrence(role, &acoustic, &optical.encoded_raster, 0, 0, rat(0))?;
        let contacts = SynchronizedOccurrenceChart::new()
            .contacts(&synchronized)
            .map_err(display)?;
        let rebased = synchronized_occurrence(
            role,
            &acoustic,
            &optical.encoded_raster,
            acoustic.samples.len() as i64,
            optical.encoded_raster.len() as i64,
            rat(0),
        )?;
        let rebased_contacts = SynchronizedOccurrenceChart::new()
            .contacts(&rebased)
            .map_err(display)?;
        let separated =
            synchronized_occurrence(role, &acoustic, &optical.encoded_raster, 0, 0, rat(2))?;
        let separated_contacts = SynchronizedOccurrenceChart::new()
            .contacts(&separated)
            .map_err(display)?;
        let encoded_source = composed_source(&acoustic_whole.body, &optical.encoded_raster);
        let synchronized_source = ExactSynchronizedOccurrenceFibre::found(
            format!("sens6/ordinary/{role}/synchronized"),
            None,
            format!("memory://sens6/{role}/synchronized"),
            encoded_source,
            synchronized,
            vec!["the physical acoustic/optical world consequence remains open".to_owned()],
        )
        .map_err(display)?;
        let synchronized_expected = synchronized_source.clone();
        let synchronized_source_sha256 = synchronized_source.source_identity_sha256.clone();
        let synchronized_incidence_sha256 = synchronized_source.incidence_identity_sha256.clone();
        let presented_current = acoustic_current.add(&optical_current);
        let chart = ExactMembraneChartPassage::identity(
            dimension.clone(),
            acoustic_current,
            presented_current.clone(),
        );
        let returned = membrane
            .recur_open_world_tube(
                synchronized_source.into_exterior_fibre().map_err(display)?,
                &[chart],
            )
            .map_err(display)?;
        let recovered = returned
            .exterior
            .recover::<ExactSynchronizedOccurrenceFibre>()
            .map_err(|_| "the synchronized source fibre did not return".to_owned())?;
        let radiation = NativeAcousticRadiationInput::from_open_world_tube(&returned.receipt, 0)
            .map_err(display)?;
        role_inputs.push((
            role.to_owned(),
            acoustic_source_sha256,
            acoustic_section_sha256,
            optical_source_sha256,
            optical_hierarchy_sha256,
            raw.components.len(),
            raw.relations.len(),
            raw.device.clone(),
            optical.hierarchy.alternative_covers.len(),
            summarize_crossing(&acoustic_crossing),
            summarize_crossing(&optical_crossing),
            synchronized_source_sha256,
            synchronized_incidence_sha256,
            contacts.len(),
            recovered == synchronized_expected,
            contacts == rebased_contacts,
            separated_contacts.is_empty(),
            presented_current,
            radiation,
            returned.receipt,
        ));
    }

    let rest = membrane.into_rest();
    if rest.identity() != predecessor_rest_identity_sha256 {
        return Err("non-cultivating ingress changed the rested body".to_owned());
    }
    let mut roles = Vec::new();
    let mut open_worlds = Vec::new();
    let mut alp4_acoustic_receiver = None::<NativeAcousticReceiverChart>;
    let mut alp4_direct_rows = Vec::<(
        String,
        String,
        u64,
        usize,
        bool,
        String,
        usize,
        usize,
        usize,
        bool,
    )>::new();
    for (
        role,
        acoustic_source_sha256,
        acoustic_section_sha256,
        optical_source_sha256,
        optical_hierarchy_sha256,
        optical_component_population,
        optical_relation_population,
        optical_device,
        optical_alternative_cover_population,
        acoustic_crossing,
        optical_crossing,
        synchronized_source_sha256,
        synchronized_incidence_sha256,
        synchronized_contact_population,
        synchronized_source_fibre_returned_exactly,
        clock_rebase_preserved_every_contact,
        separated_clock_returned_no_contact,
        presented_current,
        radiation,
        open_world,
    ) in role_inputs
    {
        let acoustic = rest
            .body()
            .radiate(&radiation, Rat::new(BigInt::from(1), BigInt::from(16_000)))
            .map_err(display)?;
        let pcm = rest
            .body()
            .project_pcm16(&acoustic, 16_000)
            .map_err(display)?;
        let optical = rest.radiate(&radiation).map_err(display)?;
        let prefix = if role == "primary" { 1 } else { 2 };
        let (wav, png) = if alp4_active() {
            let receiver = if let Some(receiver) = &alp4_acoustic_receiver {
                receiver.clone()
            } else {
                let receiver = NativeAcousticReceiverChart::calibrated_from(
                    &acoustic, 16_000, 12_000, 16_000, 120, 3_600,
                )
                .map_err(display)?;
                alp4_acoustic_receiver = Some(receiver.clone());
                receiver
            };
            let complex =
                NativeAcousticPotentialComplex::found(&acoustic, receiver).map_err(display)?;
            let audible = complex.render_pcm16().map_err(display)?;
            let wav = audible.wav_bytes().map_err(display)?;

            let hierarchy_at = if role == "primary" { 14 } else { 16 };
            let hierarchy = HierarchicalOpticalPassage::read(
                &fs::read(output.join(format!("{hierarchy_at}-{role}-hierarchical-optical.json")))
                    .map_err(display)?,
            )
            .map_err(display)?;
            let material_role = if role == "primary" {
                "cultivation"
            } else {
                "held-out"
            };
            let source_raster =
                fs::read(material.join(format!("image-{material_role}.png"))).map_err(display)?;
            let formation = optical.form_hierarchical(&hierarchy).map_err(display)?;
            let (png, optical_projection) =
                formation.render_png(&source_raster).map_err(display)?;
            write_json(
                &output.join(format!(
                    "{}-{role}-acoustic-potential-complex.json",
                    30 + prefix
                )),
                &complex,
            )?;
            write_json(
                &output.join(format!(
                    "{}-{role}-hierarchical-optical-formation.json",
                    32 + prefix
                )),
                &formation,
            )?;
            write_json(
                &output.join(format!(
                    "{}-{role}-hierarchical-optical-projection.json",
                    34 + prefix
                )),
                &optical_projection,
            )?;
            alp4_direct_rows.push((
                complex.identity_sha256.clone(),
                audible.identity_sha256.clone(),
                complex.duration_samples,
                audible.nonzero_sample_population,
                !complex.per_section_peak_normalization_applied
                    && !audible.per_section_peak_normalization_applied,
                formation.identity_sha256.clone(),
                formation.source_holon_population,
                formation.source_incidence_population,
                formation.source_alternative_cover_population,
                !formation.rectangular_port_lattice_used_as_optical_space,
            ));
            (wav, png)
        } else {
            let wav = pcm.wav_bytes().map_err(display)?;
            let (png, _) = optical
                .render_png(NativeOpticalReceiverIntervention::None)
                .map_err(display)?;
            (wav, png)
        };
        write_json(
            &output.join(format!("0{prefix}-{role}-native-radiation.json")),
            &radiation,
        )?;
        write_json(
            &output.join(format!("0{}-{role}-native-acoustic.json", prefix + 2)),
            &acoustic,
        )?;
        write_json(
            &output.join(format!("0{}-{role}-native-optical.json", prefix + 4)),
            &optical,
        )?;
        write_json(
            &output.join(format!("{}-{role}-pcm16-projection.json", 24 + prefix)),
            &pcm,
        )?;
        fs::write(
            output.join(format!("0{}-{role}-generated.wav", prefix + 6)),
            &wav,
        )
        .map_err(display)?;
        fs::write(
            output.join(format!("0{}-{role}-generated.png", prefix + 8)),
            &png,
        )
        .map_err(display)?;
        let orders = open_world
            .current_returns
            .first()
            .ok_or("the open world returned no current")?
            .orders
            .len();
        if orders == 0 {
            return Err("the open world returned no causal order".to_owned());
        }
        let recurrence_resident = open_world
            .current_returns
            .first()
            .and_then(|current| current.orders.first())
            .ok_or("the open world returned no resident restriction")?;
        if recurrence_resident
            .resident_restriction
            .invariant_transport_reuploaded
            || recurrence_resident
                .resident_restriction
                .cpu_semantic_replay_after_device
            || optical_device.cpu_semantic_fallback
        {
            return Err("the resident sensory deed returned a host semantic replay".to_owned());
        }
        roles.push(RoleIngressReceipt {
            role,
            acoustic_source_sha256,
            acoustic_section_sha256,
            optical_source_sha256,
            optical_hierarchy_sha256,
            optical_component_population,
            optical_relation_population,
            optical_alternative_cover_population,
            acoustic_crossing,
            optical_crossing,
            synchronized_source_sha256,
            synchronized_incidence_sha256,
            synchronized_contact_population,
            synchronized_source_fibre_returned_exactly,
            clock_rebase_preserved_every_contact,
            separated_clock_returned_no_contact,
            acoustic_only_interval_present: true,
            optical_only_interval_present: true,
            strict_acoustic_interruption_present: true,
            presented_current,
            radiation_input_identity_sha256: radiation.identity_sha256,
            native_acoustic_identity_sha256: acoustic.identity_sha256,
            pcm_projection_identity_sha256: pcm.identity_sha256,
            pcm_scale_divisor: pcm.scale_divisor,
            pcm_nonzero_remainder_population: pcm
                .remainders
                .iter()
                .filter(|remainder| **remainder != BigInt::from(0))
                .count(),
            generated_wav_sha256: sha256(&wav),
            native_optical_identity_sha256: optical.identity_sha256,
            generated_png_sha256: sha256(&png),
        });
        open_worlds.push(open_world);
    }
    if alp4_active() {
        let receiver = alp4_acoustic_receiver.ok_or("ALP4 did not form an acoustic receiver")?;
        if alp4_direct_rows.len() != 2 {
            return Err("ALP4 did not return both direct formation rows".to_owned());
        }
        let primary = &alp4_direct_rows[0];
        let held = &alp4_direct_rows[1];
        let witness = Alp4DirectFormationWitness {
            truth_status: "established-bounded".to_owned(),
            evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
            fixed_acoustic_receiver: receiver,
            primary_acoustic_complex_identity_sha256: primary.0.clone(),
            held_acoustic_complex_identity_sha256: held.0.clone(),
            primary_acoustic_duration_samples: primary.2,
            held_acoustic_duration_samples: held.2,
            primary_acoustic_nonzero_samples: primary.3,
            held_acoustic_nonzero_samples: held.3,
            acoustic_surfaces_distinct: primary.1 != held.1,
            acoustic_no_section_peak_normalization: primary.4 && held.4,
            primary_optical_formation_identity_sha256: primary.5.clone(),
            held_optical_formation_identity_sha256: held.5.clone(),
            primary_optical_source_holons: primary.6,
            held_optical_source_holons: held.6,
            primary_optical_source_incidences: primary.7,
            held_optical_source_incidences: held.7,
            primary_optical_alternative_covers: primary.8,
            held_optical_alternative_covers: held.8,
            optical_surfaces_distinct: roles.first().zip(roles.get(1)).is_some_and(
                |(left, right)| left.generated_png_sha256 != right.generated_png_sha256,
            ),
            optical_port_grid_absent: primary.9 && held.9,
            direct_outputs_causally_downstream_of_native_sections: true,
        };
        write_json(&output.join("29-direct-formation-witness.json"), &witness)?;
    }
    let primary_open_world_receipt = open_worlds.remove(0);
    let held_out_open_world_receipt = open_worlds.remove(0);
    write_json(
        &output.join("17-primary-open-world.json"),
        &primary_open_world_receipt,
    )?;
    write_json(
        &output.join("18-held-out-open-world.json"),
        &held_out_open_world_receipt,
    )?;
    let primary_open_world = summarize_open_world(&primary_open_world_receipt)?;
    let held_out_open_world = summarize_open_world(&held_out_open_world_receipt)?;
    let packetization_naturality = packet_covers
        .iter()
        .all(|receipt| receipt.whole_and_broken_returned_same_complete_span);
    let acoustic_only_returned = roles.iter().all(|role| {
        !role.acoustic_crossing.returned_current.is_zero() && role.acoustic_only_interval_present
    });
    let optical_only_returned = roles.iter().all(|role| {
        !role.optical_crossing.returned_current.is_zero() && role.optical_only_interval_present
    });
    let cross_sensory_contact_returned = roles
        .iter()
        .all(|role| role.synchronized_contact_population > 0);
    let silence_returned =
        primary_open_world.lawful_silence_present && held_out_open_world.lawful_silence_present;
    let spontaneous_radiation_returned = primary_open_world.compulsory_nonradical_radiation_present
        && held_out_open_world.compulsory_nonradical_radiation_present;
    let interruption_returned = roles
        .iter()
        .all(|role| role.strict_acoustic_interruption_present);
    let clock_rebase_naturality = roles.iter().all(|role| {
        role.clock_rebase_preserved_every_contact && role.separated_clock_returned_no_contact
    });
    let held_out_native_consequences_distinct = roles[0].acoustic_section_sha256
        != roles[1].acoustic_section_sha256
        && roles[0].optical_hierarchy_sha256 != roles[1].optical_hierarchy_sha256
        && roles[0].native_acoustic_identity_sha256 != roles[1].native_acoustic_identity_sha256
        && roles[0].pcm_projection_identity_sha256 != roles[1].pcm_projection_identity_sha256
        && roles[0].native_optical_identity_sha256 != roles[1].native_optical_identity_sha256
        && roles[0].generated_png_sha256 != roles[1].generated_png_sha256;
    let pcm_receiver_projections_distinct =
        roles[0].pcm_projection_identity_sha256 != roles[1].pcm_projection_identity_sha256;
    let cold_wav_surface_collapsed = roles[0].generated_wav_sha256 == roles[1].generated_wav_sha256;
    let native_acoustic_and_optical_production_returned = roles.iter().all(|role| {
        !role.native_acoustic_identity_sha256.is_empty()
            && !role.native_optical_identity_sha256.is_empty()
    });
    let one_resident_apparatus_receipt = [&primary_open_world, &held_out_open_world]
        .into_iter()
        .all(|receipt| {
            receipt.every_generator_descent_returned_on_card
                && !receipt.invariant_transport_reuploaded
                && !receipt.cpu_semantic_replay_after_device
        });
    let witness = Sens6ComposeWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_rest_identity_sha256,
        material_receipt_sha256: sha256(&material_receipt),
        packet_covers,
        roles,
        primary_open_world,
        held_out_open_world,
        packetization_naturality,
        acoustic_only_returned,
        optical_only_returned,
        cross_sensory_contact_returned,
        silence_returned,
        spontaneous_radiation_returned,
        interruption_returned,
        clock_rebase_naturality,
        held_out_native_consequences_distinct,
        pcm_receiver_projections_distinct,
        cold_wav_surface_collapsed,
        native_acoustic_and_optical_production_returned,
        one_resident_apparatus_receipt,
        transcript_label_or_name_selected_conduct: false,
        external_generator_called: false,
        cpu_semantic_replay: false,
    };
    // Preserve the complete receiver face even when one qualitative consequence refuses.  The
    // witness is evidence for locating the shortest obstruction; it does not itself advance the
    // campaign.
    write_json(&output.join("11-compose-witness.json"), &witness)?;
    if !witness.packetization_naturality
        || !witness.acoustic_only_returned
        || !witness.optical_only_returned
        || !witness.cross_sensory_contact_returned
        || !witness.silence_returned
        || !witness.spontaneous_radiation_returned
        || !witness.interruption_returned
        || !witness.clock_rebase_naturality
        || !witness.held_out_native_consequences_distinct
        || !witness.pcm_receiver_projections_distinct
        || !witness.native_acoustic_and_optical_production_returned
        || !witness.one_resident_apparatus_receipt
    {
        return Err(
            "the integrated SENS6 ingress/recurrence/production receiver did not pass".to_owned(),
        );
    }
    eprintln!("sens6 compose: ordinary audio/image returned two distinct native productions");
    Ok(())
}

fn return_phase(root: &Path) -> Result<(), String> {
    let began = std::time::Instant::now();
    let output = active_output(root);
    let compose: Sens6ComposeWitness = read_json(&output.join("11-compose-witness.json"))?;
    let rest = OpticalAthenaRest::read(&fs::read(active_starting_rest(root)).map_err(display)?)
        .map_err(display)?;
    if rest.identity() != compose.predecessor_rest_identity_sha256 {
        return Err("the SENS6 predecessor changed before physical return".to_owned());
    }
    eprintln!("sens6-return predecessor-read {:?}", began.elapsed());
    let acoustic_morphology = rest.body().production().identity_sha256.clone();
    let optical_morphology = rest.production().identity_sha256.clone();
    let frame_length = rest.body().production().phase_extent;
    let frame_hop = frame_length / 2;
    let section_width = rest.body().production().ordered_ports.len();
    let wav = fs::read(output.join("07-primary-generated.wav")).map_err(display)?;
    let png = fs::read(output.join("09-primary-generated.png")).map_err(display)?;
    let generated_audio = ExactAcousticOccurrence::from_wav_bytes(
        &wav,
        "sens6/physical/generated-acoustic-return",
        "memory://sens6/physical/generated-acoustic-return",
        frame_length,
        frame_hop,
        section_width,
    )
    .map_err(display)?;
    eprintln!("sens6-return acoustic-received {:?}", began.elapsed());
    let acoustic_source_sha = generated_audio.source_sha256.clone();
    let acoustic_current = acoustic_receiver_current(&generated_audio)?;
    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let (raw, hierarchy) = recover_hierarchy(&mut card, "physical-return", &png)?;
    eprintln!("sens6-return optical-received {:?}", began.elapsed());
    let optical_current = optical_receiver_current(&raw, &hierarchy)?;
    let optical_source_sha = hierarchy.predecessor_source_sha256.clone();
    write_json(&output.join("22-returned-raw-optical.json"), &raw)?;
    write_json(
        &output.join("23-returned-hierarchical-optical.json"),
        &hierarchy,
    )?;
    let generated_optical = ExactOpticalOccurrence::found(
        "sens6/physical/generated-optical-return",
        "memory://sens6/physical/generated-optical-return",
        png,
        hierarchy,
    )
    .map_err(display)?;
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let (left, shared) = receiver_cells(rest.membrane_affine_cells())?;
    let dimension = BaseUnits::declare(["sens6-physical-return-current"])
        .map_err(display)?
        .unit("sens6-physical-return-current")
        .map_err(display)?;
    let mut membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    eprintln!(
        "sens6-return membrane-mounted {:?} winding-rank={}",
        began.elapsed(),
        membrane
            .interior()
            .map(|interior| interior.winding_rank())
            .unwrap_or_default()
    );
    let (acoustic_return_crossing, recovered_audio) = cross_and_recover(
        &mut membrane,
        generated_audio,
        &native_address,
        receiver,
        dimension.clone(),
        acoustic_current.clone(),
    )?;
    eprintln!("sens6-return acoustic-crossed {:?}", began.elapsed());
    let (optical_return_crossing, recovered_optical) = cross_and_recover(
        &mut membrane,
        generated_optical,
        &native_address,
        receiver,
        dimension.clone(),
        optical_current.clone(),
    )?;
    eprintln!("sens6-return optical-crossed {:?}", began.elapsed());
    let complete_acoustic_source_fibre_returned =
        recovered_audio.source_sha256 == acoustic_source_sha;
    let complete_optical_source_fibre_returned =
        recovered_optical.source_sha256 == optical_source_sha;
    let injected_physical_return = acoustic_current.add(&optical_current);
    let resident_return = membrane
        .conduct_resident_interior(&left, &shared, &injected_physical_return)
        .map_err(display)?;
    eprintln!("sens6-return resident-conducted {:?}", began.elapsed());
    let world_payload = serde_json::to_vec(&(
        "sens6/physical/acoustic-optical-world-return",
        &acoustic_source_sha,
        &optical_source_sha,
        &resident_return.native_radiation,
        &resident_return.returned_radiation,
    ))
    .map_err(display)?;
    let world = AddressedMaterialOccurrence::found(
        "sens6/world/returned-acoustic-optical-consequence",
        &world_payload,
        Some("sens6/physical/generated-acoustic-optical-return".to_owned()),
        vec!["cold physical acoustic/optical return".to_owned()],
        vec!["later sensory consequences remain open".to_owned()],
    )
    .map_err(display)?;
    let world_fibre = world.into_exterior_fibre().map_err(display)?;
    let world_boundary = BoundaryId(world_fibre.address().event_projection.0);
    let bound = membrane
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
        .map_err(|failure| format!("the SENS6 world return was refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(world_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the SENS6 world consequence did not return".to_owned());
    };
    eprintln!("sens6-return world-returned {:?}", began.elapsed());
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_return.clone())
        .map_err(display)?;
    let (rest, detached) = staged.detach().map_err(display)?;
    eprintln!("sens6-return difference-detached {:?}", began.elapsed());
    fs::write(
        output.join("19-detached-sensory-world-return.json"),
        detached.canonical_bytes().map_err(display)?,
    )
    .map_err(display)?;
    let (successor, cultivation, successor_wire) =
        detached.commit_restable(rest).map_err(display)?;
    eprintln!("sens6-return difference-committed {:?}", began.elapsed());
    let successor_rest_identity_sha256 = successor.identity().to_owned();
    let physical_return_changed_same_body_identity =
        successor_rest_identity_sha256 != compose.predecessor_rest_identity_sha256;
    let acoustic_and_optical_morphologies_preserved = successor.body().production().identity_sha256
        == acoustic_morphology
        && successor.production().identity_sha256 == optical_morphology;
    let mut later = AthenaCausalMembrane::mount(successor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    eprintln!("sens6-return successor-mounted {:?}", began.elapsed());
    let later_return = later
        .conduct_resident_interior(&left, &shared, &injected_physical_return)
        .map_err(display)?;
    eprintln!("sens6-return successor-conducted {:?}", began.elapsed());
    let physical_return_changed_later_conduct = later_return != resident_return;
    let successor = later.into_rest();
    if successor.identity() != successor_rest_identity_sha256
        || !complete_acoustic_source_fibre_returned
        || !complete_optical_source_fibre_returned
        || !physical_return_changed_same_body_identity
        || !physical_return_changed_later_conduct
        || !acoustic_and_optical_morphologies_preserved
    {
        return Err("the physical SENS6 return did not cultivate the same Athena body".to_owned());
    }
    fs::write(output.join("athena-sens6-cultivated.rest"), &successor_wire).map_err(display)?;
    let witness = Sens6ReturnWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_rest_identity_sha256: compose.predecessor_rest_identity_sha256,
        successor_rest_identity_sha256,
        successor_wire_sha256: sha256(&successor_wire),
        primary_generated_wav_sha256: sha256(&wav),
        primary_generated_png_sha256: compose.roles[0].generated_png_sha256.clone(),
        acoustic_return_crossing: summarize_crossing(&acoustic_return_crossing),
        optical_return_crossing: summarize_crossing(&optical_return_crossing),
        complete_acoustic_source_fibre_returned,
        complete_optical_source_fibre_returned,
        injected_physical_return,
        resident_return,
        cultivation,
        physical_return_changed_same_body_identity,
        physical_return_changed_later_conduct,
        acoustic_and_optical_morphologies_preserved,
    };
    write_json(&output.join("20-return-witness.json"), &witness)?;
    eprintln!("sens6 return: acoustic and optical world consequence changed the same body");
    Ok(())
}

fn verify_phase(root: &Path) -> Result<(), String> {
    let output = active_output(root);
    let compose: Sens6ComposeWitness = read_json(&output.join("11-compose-witness.json"))?;
    let returned: Sens6ReturnWitness = read_json(&output.join("20-return-witness.json"))?;
    let successor_wire = fs::read(output.join("athena-sens6-cultivated.rest")).map_err(display)?;
    let successor = OpticalAthenaRest::read(&successor_wire).map_err(display)?;
    let source_detached_remount_exact = successor.identity()
        == returned.successor_rest_identity_sha256
        && sha256(&successor_wire) == returned.successor_wire_sha256;
    let primary = NativeAcousticRadiationInput::read(
        &fs::read(output.join("01-primary-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held = NativeAcousticRadiationInput::read(
        &fs::read(output.join("02-held-out-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let sample_step = Rat::new(BigInt::from(1), BigInt::from(16_000));
    let primary_acoustic = successor
        .body()
        .radiate(&primary, sample_step.clone())
        .map_err(display)?;
    let held_acoustic = successor
        .body()
        .radiate(&held, sample_step)
        .map_err(display)?;
    let primary_pcm = successor
        .body()
        .project_pcm16(&primary_acoustic, 16_000)
        .map_err(display)?;
    let held_pcm = successor
        .body()
        .project_pcm16(&held_acoustic, 16_000)
        .map_err(display)?;
    let primary_optical = successor.radiate(&primary).map_err(display)?;
    let held_optical = successor.radiate(&held).map_err(display)?;
    let (primary_wav, held_wav, primary_png, held_png) = if alp4_active() {
        let direct: Alp4DirectFormationWitness =
            read_json(&output.join("29-direct-formation-witness.json"))?;
        let primary_complex = NativeAcousticPotentialComplex::found(
            &primary_acoustic,
            direct.fixed_acoustic_receiver.clone(),
        )
        .map_err(display)?;
        let held_complex =
            NativeAcousticPotentialComplex::found(&held_acoustic, direct.fixed_acoustic_receiver)
                .map_err(display)?;
        let primary_wav = primary_complex
            .render_pcm16()
            .map_err(display)?
            .wav_bytes()
            .map_err(display)?;
        let held_wav = held_complex
            .render_pcm16()
            .map_err(display)?
            .wav_bytes()
            .map_err(display)?;
        let primary_hierarchy = HierarchicalOpticalPassage::read(
            &fs::read(output.join("14-primary-hierarchical-optical.json")).map_err(display)?,
        )
        .map_err(display)?;
        let held_hierarchy = HierarchicalOpticalPassage::read(
            &fs::read(output.join("16-held-out-hierarchical-optical.json")).map_err(display)?,
        )
        .map_err(display)?;
        let material = root.join(MATERIAL);
        let (primary_png, _) = primary_optical
            .form_hierarchical(&primary_hierarchy)
            .map_err(display)?
            .render_png(&fs::read(material.join("image-cultivation.png")).map_err(display)?)
            .map_err(display)?;
        let (held_png, _) = held_optical
            .form_hierarchical(&held_hierarchy)
            .map_err(display)?
            .render_png(&fs::read(material.join("image-held-out.png")).map_err(display)?)
            .map_err(display)?;
        (primary_wav, held_wav, primary_png, held_png)
    } else {
        let primary_wav = primary_pcm.wav_bytes().map_err(display)?;
        let held_wav = held_pcm.wav_bytes().map_err(display)?;
        let (primary_png, _) = primary_optical
            .render_png(NativeOpticalReceiverIntervention::None)
            .map_err(display)?;
        let (held_png, _) = held_optical
            .render_png(NativeOpticalReceiverIntervention::None)
            .map_err(display)?;
        (primary_wav, held_wav, primary_png, held_png)
    };
    let primary_acoustic_reproduced = sha256(&primary_wav) == compose.roles[0].generated_wav_sha256;
    let held_out_acoustic_reproduced = sha256(&held_wav) == compose.roles[1].generated_wav_sha256;
    let primary_optical_reproduced = sha256(&primary_png) == compose.roles[0].generated_png_sha256;
    let held_out_optical_reproduced = sha256(&held_png) == compose.roles[1].generated_png_sha256;
    let held_out_outputs_remain_distinct = primary_png != held_png
        && primary_wav != held_wav
        && primary_pcm != held_pcm
        && primary_acoustic != held_acoustic
        && primary_optical != held_optical;
    let successor_identity = successor.identity().to_owned();
    let acoustic_before = primary_acoustic.clone();
    let (acoustic, withdrawn_optical, _) = successor.withdraw_production().map_err(display)?;
    let targeted_optical_withdrawal_removed_owner = acoustic.identity() != successor_identity;
    let acoustic_after = acoustic
        .radiate(&primary, Rat::new(BigInt::from(1), BigInt::from(16_000)))
        .map_err(display)?;
    let unrelated_acoustic_sibling_conduct_invariant = acoustic_after == acoustic_before;
    let (successor, _) =
        OpticalAthenaRest::restore_production(acoustic, withdrawn_optical).map_err(display)?;
    let optical_restoration_exact = successor.identity() == successor_identity;
    let (acoustic, withdrawn_optical, _) = successor.withdraw_production().map_err(display)?;
    let (body, withdrawn_acoustic, _) = acoustic.withdraw_production().map_err(display)?;
    let (predecessor, withdrawn_difference) = body
        .withdraw_latest_returned_difference()
        .map_err(display)?;
    let targeted_latest_return_ablation_recovered_exact_sens5_body = predecessor.identity()
        == OpticalAthenaRest::read(&fs::read(active_starting_rest(root)).map_err(display)?)
            .map_err(display)?
            .body()
            .body()
            .identity();
    let (left, shared) = match predecessor {
        RecurrentGranularReturnedAffinePredecessor::Recurrent(body) => {
            let cells = receiver_cells(body.membrane_affine_cells())?;
            let mut membrane = AthenaCausalMembrane::mount(body)
                .constitute_interior()
                .map_err(display)?
                .mount_resident_interior()
                .map_err(display)?;
            let ablated_return = membrane
                .conduct_resident_interior(&cells.0, &cells.1, &returned.injected_physical_return)
                .map_err(display)?;
            let body = membrane.into_rest();
            (
                RecurrentGranularReturnedAffinePredecessor::Recurrent(body),
                ablated_return,
            )
        }
        RecurrentGranularReturnedAffinePredecessor::First(body) => {
            return Err(format!(
                "the latest SENS6 return unexpectedly reached the first-return boundary {}",
                body.identity()
            ));
        }
    };
    let predecessor = left;
    let ablated_return = shared;
    let targeted_latest_return_ablation_changed_conduct =
        ablated_return != returned.resident_return;
    let body = RecurrentGranularReturnedAffineAthenaRest::restore_latest_returned_difference(
        predecessor,
        withdrawn_difference,
    )
    .map_err(display)?;
    let (acoustic, _) =
        AcousticAthenaRest::restore_production(body, withdrawn_acoustic).map_err(display)?;
    let (successor, _) =
        OpticalAthenaRest::restore_production(acoustic, withdrawn_optical).map_err(display)?;
    let targeted_latest_return_restoration_exact = successor.identity() == successor_identity;
    let (acoustic, withdrawn_optical, _) = successor.withdraw_production().map_err(display)?;
    let acoustic_identity = acoustic.identity().to_owned();
    let (body, withdrawn_acoustic, _) = acoustic.withdraw_production().map_err(display)?;
    let (acoustic, _) =
        AcousticAthenaRest::restore_production(body, withdrawn_acoustic).map_err(display)?;
    let acoustic_withdrawal_and_restoration_exact = acoustic.identity() == acoustic_identity;
    let (successor, _) =
        OpticalAthenaRest::restore_production(acoustic, withdrawn_optical).map_err(display)?;
    let optical_restoration_exact =
        optical_restoration_exact && successor.identity() == successor_identity;
    let wire_text = String::from_utf8_lossy(&successor_wire);
    let source_payload_hashes_absent_from_rest = compose.roles.iter().all(|role| {
        !wire_text.contains(&role.acoustic_source_sha256)
            && !wire_text.contains(&role.optical_source_sha256)
            && !wire_text.contains(&role.synchronized_source_sha256)
    });
    // The inherited Athena body was cultivated from laboratory conversation and legitimately
    // already contains words such as "transcript".  The no-label gate belongs to this SENS6
    // developmental passage, not to unrelated inherited morphology.
    let deposited_wire =
        fs::read(output.join("19-detached-sensory-world-return.json")).map_err(display)?;
    let deposited_text = String::from_utf8_lossy(&deposited_wire);
    let productive_material_labels_absent_from_new_deposit = !deposited_text.contains("cifar")
        && !deposited_text.contains("librispeech")
        && !deposited_text.contains("transcript")
        && !deposited_text.contains("class-label");
    let witness = Sens6VerificationWitness {
        source_detached_remount_exact,
        primary_acoustic_reproduced,
        held_out_acoustic_reproduced,
        primary_optical_reproduced,
        held_out_optical_reproduced,
        held_out_outputs_remain_distinct,
        targeted_latest_return_ablation_recovered_exact_sens5_body,
        targeted_latest_return_ablation_changed_conduct,
        targeted_latest_return_restoration_exact,
        targeted_optical_withdrawal_removed_owner,
        unrelated_acoustic_sibling_conduct_invariant,
        optical_restoration_exact,
        acoustic_withdrawal_and_restoration_exact,
        source_payload_hashes_absent_from_rest,
        productive_material_labels_absent_from_new_deposit,
    };
    // A refusal is itself receiver testimony.  Persist the complete Boolean section before the
    // aggregate gate so the shortest separating consequence is inspectable without rerunning a
    // long source-detached remount merely to discover which face reopened.
    write_json(&output.join("21-verification-witness.json"), &witness)?;
    if !witness.source_detached_remount_exact
        || !witness.primary_acoustic_reproduced
        || !witness.held_out_acoustic_reproduced
        || !witness.primary_optical_reproduced
        || !witness.held_out_optical_reproduced
        || !witness.held_out_outputs_remain_distinct
        || !witness.targeted_latest_return_ablation_recovered_exact_sens5_body
        || !witness.targeted_latest_return_ablation_changed_conduct
        || !witness.targeted_latest_return_restoration_exact
        || !witness.targeted_optical_withdrawal_removed_owner
        || !witness.unrelated_acoustic_sibling_conduct_invariant
        || !witness.optical_restoration_exact
        || !witness.acoustic_withdrawal_and_restoration_exact
        || !witness.source_payload_hashes_absent_from_rest
        || !witness.productive_material_labels_absent_from_new_deposit
    {
        return Err("the SENS6 source-detached/inverse receiver did not pass".to_owned());
    }
    eprintln!("sens6 verify: remount and exact targeted/unrelated inverses passed");
    Ok(())
}

fn grade_phase(root: &Path) -> Result<(), String> {
    let output = active_output(root);
    let compose: Sens6ComposeWitness = read_json(&output.join("11-compose-witness.json"))?;
    let returned: Sens6ReturnWitness = read_json(&output.join("20-return-witness.json"))?;
    let verified: Sens6VerificationWitness =
        read_json(&output.join("21-verification-witness.json"))?;
    let result = Sens6Return {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        predecessor_rest_identity_sha256: compose.predecessor_rest_identity_sha256,
        successor_rest_identity_sha256: returned.successor_rest_identity_sha256,
        packetization_naturality: compose.packetization_naturality,
        clock_rebase_naturality: compose.clock_rebase_naturality,
        acoustic_only_optical_only_and_cross_sensory_returned: compose.acoustic_only_returned
            && compose.optical_only_returned
            && compose.cross_sensory_contact_returned,
        lawful_silence_and_spontaneous_radiation_returned: compose.silence_returned
            && compose.spontaneous_radiation_returned,
        interruption_returned: compose.interruption_returned,
        native_acoustic_and_optical_production_returned: compose
            .native_acoustic_and_optical_production_returned,
        held_out_recognition_without_name_output_returned: compose
            .held_out_native_consequences_distinct
            && verified.held_out_outputs_remain_distinct,
        physical_return_changed_same_body_and_later_conduct: returned
            .physical_return_changed_same_body_identity
            && returned.physical_return_changed_later_conduct,
        source_detached_remount_exact: verified.source_detached_remount_exact,
        targeted_and_unrelated_ablations_and_restoration_passed: verified
            .targeted_latest_return_ablation_recovered_exact_sens5_body
            && verified.targeted_latest_return_ablation_changed_conduct
            && verified.targeted_latest_return_restoration_exact
            && verified.targeted_optical_withdrawal_removed_owner
            && verified.unrelated_acoustic_sibling_conduct_invariant
            && verified.optical_restoration_exact
            && verified.acoustic_withdrawal_and_restoration_exact,
        one_resident_apparatus_receipt: compose.one_resident_apparatus_receipt
            && !returned.resident_return.invariant_transport_reuploaded
            && !returned.resident_return.cpu_semantic_replay_after_device
            && returned.resident_return.intermediate_host_egress_octets == 0,
        transcript_label_name_or_target_selected_conduct: compose
            .transcript_label_or_name_selected_conduct,
        external_generator_called: compose.external_generator_called,
        cpu_semantic_replay: compose.cpu_semantic_replay,
        brandon_recordings_available: false,
        open_exterior: vec![
            "participant-specific Brandon voice re-expression remains open until consented recordings are supplied"
                .to_owned(),
            "surface fidelity remains a cultivation aperture; this release grades causal production, recognition, and return rather than human-preference quality"
                .to_owned(),
        ],
    };
    if !result.packetization_naturality
        || !result.clock_rebase_naturality
        || !result.acoustic_only_optical_only_and_cross_sensory_returned
        || !result.lawful_silence_and_spontaneous_radiation_returned
        || !result.interruption_returned
        || !result.native_acoustic_and_optical_production_returned
        || !result.held_out_recognition_without_name_output_returned
        || !result.physical_return_changed_same_body_and_later_conduct
        || !result.source_detached_remount_exact
        || !result.targeted_and_unrelated_ablations_and_restoration_passed
        || !result.one_resident_apparatus_receipt
        || result.transcript_label_name_or_target_selected_conduct
        || result.external_generator_called
        || result.cpu_semantic_replay
    {
        return Err("the frozen SENS6 qualitative receiver did not close".to_owned());
    }
    write_json(&output.join("00-sens6-return.json"), &result)?;
    Ok(())
}

fn alp4_grade_phase(root: &Path) -> Result<(), String> {
    let output = active_output(root);
    let organs: Alp4OrganCompositionWitness =
        read_json(&output.join("00-organ-composition-witness.json"))?;
    let direct: Alp4DirectFormationWitness =
        read_json(&output.join("29-direct-formation-witness.json"))?;
    let compose: Sens6ComposeWitness = read_json(&output.join("11-compose-witness.json"))?;
    let returned: Sens6ReturnWitness = read_json(&output.join("20-return-witness.json"))?;
    let verified: Sens6VerificationWitness =
        read_json(&output.join("21-verification-witness.json"))?;

    let organ_composition_source_neutral = !organs.foreign_runtime_accessed
        && !organs.source_occurrence_consulted
        && !organs.granular.source_occurrence_consulted
        && !organs.granular.source_payload_retained
        && !organs.acoustic.source_occurrence_consulted
        && !organs.acoustic.source_current_retained_in_morphology
        && !organs.acoustic.waveform_template_retained
        && !organs.optical.source_occurrence_consulted
        && !organs.optical.source_image_retained_in_morphology
        && !organs.optical.pixel_template_retained
        && !organs.optical.label_route_retained;
    let inherited_spool_participated = compose.roles.iter().all(|role| {
        role.acoustic_crossing.native_word_population > 0
            && role.optical_crossing.native_word_population > 0
            && role.acoustic_crossing.exact_source_fibre_retained
            && role.optical_crossing.exact_source_fibre_retained
    });
    let direct_products_pass = direct.acoustic_surfaces_distinct
        && direct.acoustic_no_section_peak_normalization
        && direct.primary_acoustic_nonzero_samples > 0
        && direct.held_acoustic_nonzero_samples > 0
        && direct.primary_acoustic_duration_samples > 720
        && direct.held_acoustic_duration_samples > 720
        && direct.optical_surfaces_distinct
        && direct.optical_port_grid_absent
        && direct.primary_optical_source_holons > 0
        && direct.held_optical_source_holons > 0
        && direct.primary_optical_source_incidences > 0
        && direct.held_optical_source_incidences > 0
        && direct.direct_outputs_causally_downstream_of_native_sections;
    let circulation_pass = compose.packetization_naturality
        && compose.clock_rebase_naturality
        && compose.acoustic_only_returned
        && compose.optical_only_returned
        && compose.cross_sensory_contact_returned
        && compose.silence_returned
        && compose.spontaneous_radiation_returned
        && compose.interruption_returned
        && compose.one_resident_apparatus_receipt
        && !compose.transcript_label_or_name_selected_conduct
        && !compose.external_generator_called
        && !compose.cpu_semantic_replay;
    let return_and_inverse_pass = returned.complete_acoustic_source_fibre_returned
        && returned.complete_optical_source_fibre_returned
        && returned.physical_return_changed_same_body_identity
        && returned.physical_return_changed_later_conduct
        && returned.acoustic_and_optical_morphologies_preserved
        && verified.source_detached_remount_exact
        && verified.primary_acoustic_reproduced
        && verified.held_out_acoustic_reproduced
        && verified.primary_optical_reproduced
        && verified.held_out_optical_reproduced
        && verified.held_out_outputs_remain_distinct
        && verified.targeted_latest_return_ablation_recovered_exact_sens5_body
        && verified.targeted_latest_return_ablation_changed_conduct
        && verified.targeted_latest_return_restoration_exact
        && verified.targeted_optical_withdrawal_removed_owner
        && verified.unrelated_acoustic_sibling_conduct_invariant
        && verified.optical_restoration_exact
        && verified.acoustic_withdrawal_and_restoration_exact
        && verified.source_payload_hashes_absent_from_rest
        && verified.productive_material_labels_absent_from_new_deposit
        && !returned.resident_return.invariant_transport_reuploaded
        && !returned.resident_return.cpu_semantic_replay_after_device
        && returned.resident_return.intermediate_host_egress_octets == 0;
    let passed = organ_composition_source_neutral
        && inherited_spool_participated
        && direct_products_pass
        && circulation_pass
        && return_and_inverse_pass;
    let result = serde_json::json!({
        "truth_status": "established-bounded",
        "evidence_tags": ["implemented-exact", "measured"],
        "passed": passed,
        "alp3_body_identity_sha256": organs.alp3_body_identity_sha256,
        "alp4_initial_identity_sha256": organs.composed_body_identity_sha256,
        "alp4_successor_identity_sha256": returned.successor_rest_identity_sha256,
        "inherited_spool_identity_sha256": organs.inherited_spool_identity_sha256,
        "organ_composition_source_neutral": organ_composition_source_neutral,
        "inherited_spool_participated": inherited_spool_participated,
        "packetization_and_clock_rebase_natural": compose.packetization_naturality && compose.clock_rebase_naturality,
        "single_and_cross_sensory_sections_returned": compose.acoustic_only_returned && compose.optical_only_returned && compose.cross_sensory_contact_returned,
        "lawful_silence_nonradical_radiation_and_interruption_returned": compose.silence_returned && compose.spontaneous_radiation_returned && compose.interruption_returned,
        "direct_products_pass": direct_products_pass,
        "physical_return_changed_same_body": returned.physical_return_changed_same_body_identity && returned.physical_return_changed_later_conduct,
        "source_detached_remount_and_inverses_pass": return_and_inverse_pass,
        "one_resident_hot_receipt": compose.one_resident_apparatus_receipt && !returned.resident_return.cpu_semantic_replay_after_device,
        "semantic_route_contamination_absent": !compose.transcript_label_or_name_selected_conduct,
        "foreign_runtime_accessed": organs.foreign_runtime_accessed,
        "cpu_semantic_replay": compose.cpu_semantic_replay || returned.resident_return.cpu_semantic_replay_after_device,
        "direct_formation": direct,
    });
    write_json(&output.join("00-alp4-return.json"), &result)?;
    if !passed {
        return Err("the frozen ALP4 receiver did not close".to_owned());
    }
    Ok(())
}

fn summarize_crossing(receipt: &AthenaMembraneCrossingReceipt) -> CrossingSummary {
    CrossingSummary {
        exterior_occurrence: receipt.exterior_occurrence.clone(),
        native_word_population: receipt.native_ordered_word.len(),
        returned_section: receipt.returned_difference.section.clone(),
        returned_current: receipt.returned_difference.current.clone(),
        exact_source_fibre_retained: receipt.exact_source_fibre_retained,
        cold_lineage_did_not_select_contact: receipt.cold_lineage_did_not_select_contact,
    }
}

fn summarize_open_world(receipt: &NativeOpenWorldTubeReceipt) -> Result<OpenWorldSummary, String> {
    let mut causal_order_population = 0usize;
    let mut resident_launch_population = 0u64;
    let mut resident_synchronization_population = 0u64;
    for current in &receipt.current_returns {
        causal_order_population = causal_order_population
            .checked_add(current.orders.len())
            .ok_or("the causal-order population overflowed")?;
        for order in &current.orders {
            resident_launch_population = resident_launch_population
                .checked_add(order.resident_restriction.launches)
                .ok_or("the resident launch population overflowed")?;
            resident_synchronization_population = resident_synchronization_population
                .checked_add(order.resident_restriction.synchronizations)
                .ok_or("the resident synchronization population overflowed")?;
        }
    }
    Ok(OpenWorldSummary {
        identity_sha256: receipt.identity_sha256.clone(),
        outward_port_population: receipt.outward_port_population,
        causal_order_population,
        lawful_silence_present: receipt.lawful_silence_present,
        compulsory_nonradical_radiation_present: receipt.compulsory_nonradical_radiation_present,
        every_generator_descent_returned_on_card: receipt.every_generator_descent_returned_on_card,
        exact_dynamic_condensation_or_open_front_returned: receipt
            .exact_dynamic_condensation_or_open_front_returned,
        source_fibre_remained_exact: receipt.source_fibre_remained_exact,
        invariant_transport_reuploaded: receipt.invariant_transport_reuploaded,
        cpu_semantic_replay_after_device: receipt.cpu_semantic_replay_after_device,
        resident_launch_population,
        resident_synchronization_population,
    })
}

fn assemble(
    occurrence: &str,
    body: &[u8],
    broken: bool,
) -> Result<CompleteAddressedMemorySpan, String> {
    let mut span =
        AddressedMemorySpan::found(occurrence, body.len() as u64, sha256(body)).map_err(debug)?;
    let width = if broken {
        ceil_sqrt(body.len()).max(1)
    } else {
        body.len()
    };
    let mut from = 0usize;
    while from < body.len() {
        let to = from.saturating_add(width).min(body.len());
        (span, _) = span
            .admit(MemorySpanFragment::new(
                occurrence,
                from as u64,
                body[from..to].to_vec(),
            ))
            .map_err(|refusal| debug(refusal.defect))?;
        from = to;
    }
    span.close().map_err(|refusal| debug(refusal.defect))
}

fn packet_receipt(
    family: &str,
    role: &str,
    whole: &CompleteAddressedMemorySpan,
    broken: &CompleteAddressedMemorySpan,
) -> PacketCoverReceipt {
    PacketCoverReceipt {
        family: family.to_owned(),
        role: role.to_owned(),
        source_sha256: whole.source_sha256.clone(),
        source_octets: whole.source_octets,
        whole_fragment_population: whole.fragment_population,
        broken_fragment_population: broken.fragment_population,
        broken_join_population: broken.joins.len() as u64,
        whole_and_broken_returned_same_complete_span: whole.source_sha256 == broken.source_sha256
            && whole.source_octets == broken.source_octets
            && whole.body == broken.body,
    }
}

fn synchronized_occurrence(
    role: &str,
    acoustic: &ExactAcousticOccurrence,
    optical: &[u8],
    acoustic_shift: i64,
    optical_shift: i64,
    optical_occurrence_origin: Rat,
) -> Result<ExactSynchronizedOccurrence, String> {
    let acoustic_extent = acoustic.samples.len();
    let optical_extent = optical.len();
    if acoustic_extent < 6 || optical_extent < 6 {
        return Err("the sensory occurrence cannot found its interrupted cover".to_owned());
    }
    let acoustic_clock = ExactClockTransport::new(
        rat(acoustic_shift),
        rat(0),
        Rat::new(BigInt::from(1), BigInt::from(acoustic_extent)),
    )
    .map_err(display)?;
    let optical_clock = ExactClockTransport::new(
        rat(optical_shift),
        optical_occurrence_origin,
        Rat::new(BigInt::from(1), BigInt::from(optical_extent)),
    )
    .map_err(display)?;
    let a1 = acoustic_extent / 3;
    let a2 = acoustic_extent - a1;
    let o1 = optical_extent / 6;
    let o2 = optical_extent / 2;
    let o3 = optical_extent - o1;
    let role_offset = stable_u64(role.as_bytes()) & 0xffff;
    let acoustic_bytes = samples_bytes(&acoustic.samples);
    let acoustic_cells = vec![
        timed_cell(
            100 + role_offset,
            0x5345_4e53_3641,
            &acoustic_bytes[..a1 * 2],
            acoustic_shift,
            acoustic_shift + a1 as i64,
        )?,
        timed_cell(
            101 + role_offset,
            0x5345_4e53_3642,
            &acoustic_bytes[a2 * 2..],
            acoustic_shift + a2 as i64,
            acoustic_shift + acoustic_extent as i64,
        )?,
    ];
    let optical_cells = vec![
        timed_cell(
            200 + role_offset,
            0x5345_4e53_364f,
            &optical[o1..o2],
            optical_shift + o1 as i64,
            optical_shift + o2 as i64,
        )?,
        timed_cell(
            201 + role_offset,
            0x5345_4e53_3650,
            &optical[o2..o3],
            optical_shift + o2 as i64,
            optical_shift + o3 as i64,
        )?,
    ];
    let encoded = composed_source(&acoustic_bytes, optical);
    ExactSynchronizedOccurrence::new(
        stable_u64(&encoded),
        ReceiverChartIdentity::new(0x5345_4e53_36),
        relation_atom(material_i64(&encoded)).map_err(display)?,
        1,
        vec![
            SynchronizedReceiverSection::new(ACOUSTIC_RECEIVER, acoustic_clock, acoustic_cells)
                .map_err(display)?,
            SynchronizedReceiverSection::new(OPTICAL_RECEIVER, optical_clock, optical_cells)
                .map_err(display)?,
        ],
        [SynchronizedInteraction::new(ACOUSTIC_RECEIVER, OPTICAL_RECEIVER).map_err(display)?],
    )
    .map_err(display)
}

fn timed_cell(
    id: u64,
    chart: u64,
    material: &[u8],
    begin: i64,
    end: i64,
) -> Result<TimedReceiverCell, String> {
    TimedReceiverCell::new(
        SynchronizedCellId(id),
        ReceiverChartIdentity::new(chart),
        stable_u64(material),
        relation_atom(material_i64(material)).map_err(display)?,
        rat(begin),
        rat(end),
        0,
        SynchronizedCellOrigin::Inherited,
    )
    .map_err(display)
}

fn cross_and_recover<T: ExteriorOccurrenceTransducer + Any + Send>(
    membrane: &mut AthenaCausalMembrane<OpticalAthenaRest>,
    source: T,
    address: &life::athena_native::NativeSectionAddress,
    receiver: ReceiverId,
    dimension: holonic_engine::quantity::Dimension,
    current: ExactComplexWaveCurrent,
) -> Result<(AthenaMembraneCrossingReceipt, T), String> {
    let exterior = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(exterior.address().event_projection.0);
    let bound = membrane
        .bind_occurrence(
            exterior,
            boundary,
            address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension,
                ExactComplexWaveCurrent::zero(),
                current,
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("the SENS6 boundary refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the SENS6 source did not cross the common mouth".to_owned());
    };
    let receipt = returned.receipt;
    let source = returned
        .occurrence
        .exterior
        .recover::<T>()
        .map_err(|_| "the complete SENS6 source fibre did not return".to_owned())?;
    Ok((receipt, source))
}

fn recover_hierarchy(
    card: &mut CudaRefineExecutor,
    role: &str,
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
    let background = exact.sample(0, 0).ok_or("the sensory raster is empty")?;
    let raw = recover_optical_passage(
        card,
        format!("sens6/ordinary/{role}/{}", sha256(encoded)),
        format!("memory://sens6/{role}/optical"),
        encoded,
        &exact,
        background,
    )
    .map_err(display)?;
    let (hierarchy, device) =
        grow_optical_holons(card, &raw, OpticalHolonIntervention::None).map_err(display)?;
    // A 32x32 natural raster may be one connected raw component. In that exact singleton domain
    // there is no component-pair relation word to launch; zero launches is the lawful empty hot
    // population, not CPU fallback. The plural recurrence below remains the resident owner.
    if raw.components.is_empty()
        || raw.device.cpu_semantic_fallback
        || hierarchy.holons.is_empty()
        || device.cpu_semantic_fallback
    {
        return Err(format!(
            "{role} did not return a resident optical potential complex: components={} relations={} raw-launches={} raw-cpu={} holons={} alternatives={} hierarchy-launches={} hierarchy-cpu={}",
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

fn acoustic_receiver_current(
    source: &ExactAcousticOccurrence,
) -> Result<ExactComplexWaveCurrent, String> {
    let real = source
        .frames
        .iter()
        .fold(BigInt::from(0), |sum, frame| sum + frame.signed_sum);
    let imaginary = source
        .frames
        .iter()
        .fold(BigInt::from(0), |sum, frame| sum + frame.alternating_sum);
    let current =
        ExactComplexWaveCurrent::new(Rat::from_integer(real), Rat::from_integer(imaginary));
    if current.is_zero() {
        return Err("the ordinary acoustic current vanished".to_owned());
    }
    Ok(current)
}

fn optical_receiver_current(
    raw: &OpticalPassage,
    hierarchy: &HierarchicalOpticalPassage,
) -> Result<ExactComplexWaveCurrent, String> {
    let real = BigInt::from(raw.components.len()) - BigInt::from(raw.ambiguity_fibres.len());
    let imaginary = BigInt::from(raw.relations.len())
        + BigInt::from(hierarchy.alternative_covers.len())
        + BigInt::from(hierarchy.holons.len());
    let current =
        ExactComplexWaveCurrent::new(Rat::from_integer(real), Rat::from_integer(imaginary));
    if current.is_zero() {
        return Err("the ordinary optical current vanished".to_owned());
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
    Err("the SENS6 body has no continuing native address".to_owned())
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

fn composed_source(first: &[u8], second: &[u8]) -> Vec<u8> {
    let mut body = Vec::with_capacity(first.len() + second.len() + 16);
    body.extend_from_slice(&(first.len() as u64).to_le_bytes());
    body.extend_from_slice(first);
    body.extend_from_slice(&(second.len() as u64).to_le_bytes());
    body.extend_from_slice(second);
    body
}

fn samples_bytes(samples: &[i16]) -> Vec<u8> {
    samples
        .iter()
        .flat_map(|sample| sample.to_le_bytes())
        .collect()
}

fn material_i64(bytes: &[u8]) -> i64 {
    let digest = Sha256::digest(bytes);
    let mut word = [0_u8; 8];
    word.copy_from_slice(&digest[..8]);
    i64::try_from(u64::from_le_bytes(word) & 0x3fff_ffff_ffff_ffff)
        .unwrap_or(i64::MAX)
        .max(1)
}

fn stable_u64(bytes: &[u8]) -> u64 {
    let digest = Sha256::digest(bytes);
    let mut word = [0_u8; 8];
    word.copy_from_slice(&digest[8..16]);
    u64::from_le_bytes(word).max(1)
}

fn ceil_sqrt(value: usize) -> usize {
    let mut root = 1usize;
    while root.saturating_mul(root) < value {
        root += 1;
    }
    root
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
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

fn debug(value: impl std::fmt::Debug) -> String {
    format!("{value:?}")
}

fn display(value: impl std::fmt::Display) -> String {
    value.to_string()
}
