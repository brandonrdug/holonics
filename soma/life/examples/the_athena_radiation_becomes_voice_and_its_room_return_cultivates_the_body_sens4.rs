//! SENS4 receiver: native Athena radiation becomes an exact acoustic current before PCM, crosses
//! a measured room, meets another speaker under overlapping clocks, and returns to cultivate the
//! same source-detached body. The phased apparatus keeps every process below the campaign's
//! three-minute ceiling without replaying SENS3.

use std::{
    collections::BTreeSet,
    env, fs,
    num::NonZeroUsize,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    cuda_refine::ResidentMembraneInteriorReturn, quantity::BaseUnits,
    receive_phase_transport_spectrum, receiver_exact_compression::ReceiverId, BoundaryId,
    CausalWorld, CpuExecutor, EventId, ExactComplexWaveCurrent, ExactPhaseCurrentSection,
    ExactWavePropagationLaw, ExactWaveSection, PhaseCurrentLineageId, PhaseCurrentReceiverId,
    WaveConditioningEvent, WaveGenerationEvent, WaveInteractionId, WaveInteractionSpec,
    WaveLineageId, WavePredictionReturnEvent, WavePropagationEvent, WavePropagationRadiation,
    WavePropagationSpec, WaveReceiverId, WaveReceiverSpec,
};
use holonic_structure::CausalMembrane;
use life::native_intelligence::{
    AcousticProductRest, AddressedMaterialOccurrence, ExactMembraneChartPassage,
    ExteriorOccurrenceTransducer, MembraneConsequence, MembraneCultivationReceipt,
    MembraneStanding, NativeAcousticCultivationReceipt, NativeAcousticProductionSection,
    NativeAcousticRadiationInput, NativeAcousticRadiationOrder, NativeAcousticReceiverCurrent,
    NativeAcousticStandingMutation, NativeCausalMembrane, NativeOpenWorldTubeTerminal,
    NativeOutwardPortReturn, RecurrentGranularReturnedAffineEcologyRest, StagedMembraneCultivation,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const PREDECESSOR: &str = concat!(
    "output/the_synchronized_sensory_world_tube_cultivates_one_athena_body_sens2/",
    "athena-synchronized-sensory.rest"
);
const SENS3: &str = "output/the_open_athena_world_tube_recurs_and_returns_lawful_silence_sens3";
const OUTPUT: &str =
    "output/the_athena_radiation_becomes_voice_and_its_room_return_cultivates_the_body_sens4";
const RIR: &str = concat!(
    "/home/b/Workspaces/laboratory/runs/information-flow-datasets/source/",
    "RIRS_NOISES/real_rirs_isotropic_noises/air_type1_air_binaural_aula_carolina_1_7_90_3.wav"
);
const OTHER_SPEAKER: &str = concat!(
    "/home/b/Workspaces/laboratory/runs/information-flow-datasets/source/",
    "LibriSpeech/dev-clean/3081/166546/3081-166546-0059.flac"
);
const SAMPLE_RATE: u32 = 16_000;

#[derive(Deserialize)]
struct StoredSens3Probe {
    #[serde(flatten)]
    _other: serde_json::Map<String, serde_json::Value>,
    native_return: StoredOpenWorldTube,
}

#[derive(Deserialize)]
struct StoredOpenWorldTube {
    rested_identity_sha256: String,
    identity_sha256: String,
    outward_port_population: usize,
    current_returns: Vec<StoredCurrentReturn>,
    #[serde(flatten)]
    _other: serde_json::Map<String, serde_json::Value>,
}

#[derive(Deserialize)]
struct StoredCurrentReturn {
    source_section: u64,
    orders: Vec<StoredOrder>,
    terminal: NativeOpenWorldTubeTerminal,
    #[serde(flatten)]
    _other: serde_json::Map<String, serde_json::Value>,
}

#[derive(Deserialize)]
struct StoredOrder {
    causal_order: u64,
    outward_port_returns: Vec<NativeOutwardPortReturn>,
    #[serde(flatten)]
    _other: serde_json::Map<String, serde_json::Value>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens4FoundationWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_identity_sha256: String,
    acoustic_rest_identity_sha256: String,
    acoustic_rest_wire_sha256: String,
    cultivation: NativeAcousticCultivationReceipt,
    primary_radiation_identity_sha256: String,
    held_out_radiation_identity_sha256: String,
    primary_production_identity_sha256: String,
    held_out_production_identity_sha256: String,
    primary_pcm_identity_sha256: String,
    held_out_pcm_identity_sha256: String,
    phase_extent_derived_from_ports_and_quadratures: u32,
    causal_order_population: usize,
    exact_waveforms_distinct_before_playback: bool,
    held_out_section_absent_from_cultivation: bool,
    source_current_absent_from_morphology: bool,
    waveform_template_absent: bool,
    source_detached_remount_reproduced_primary: bool,
    source_detached_remount_reproduced_held_out: bool,
    targeted_withdrawal_removed_production_owner: bool,
    targeted_restoration_exact: bool,
    withdrawal: NativeAcousticStandingMutation,
    restoration: NativeAcousticStandingMutation,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ExactAcousticInterval {
    lineage: PhaseCurrentLineageId,
    begin_sample: u64,
    end_sample: u64,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens4RoomWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    primary_production_identity_sha256: String,
    room_response_path: String,
    room_response_sha256: String,
    other_speaker_path: String,
    other_speaker_sha256: String,
    sample_rate: u32,
    exact_sample_step: Rat,
    native_phase_extent: u32,
    native_sample_population: usize,
    room_channel_population: usize,
    room_sample_population_per_channel: usize,
    other_speaker_sample_population: usize,
    exact_phase_spectrum_sha256: Vec<String>,
    exact_wave_transition_receipts_sha256: String,
    exact_wave_mode_population: usize,
    generated_before_return_population: usize,
    exact_return_grade_population: usize,
    obstructed_return_grade_population: usize,
    room_impulse_intervals: Vec<ExactAcousticInterval>,
    self_echo_intervals: Vec<ExactAcousticInterval>,
    other_speaker_interval: ExactAcousticInterval,
    overlap_interval: ExactAcousticInterval,
    interruption_interval: ExactAcousticInterval,
    room_impulse_lineages_distinct: bool,
    self_echo_lineages_distinct: bool,
    other_speaker_lineage_distinct: bool,
    overlap_present: bool,
    strict_interruption_present: bool,
    exact_self_echo_left_current: Rat,
    exact_self_echo_right_current: Rat,
    exact_other_speaker_current: Rat,
    exact_microphone_return: ExactComplexWaveCurrent,
    resident_receiver_current: NativeAcousticReceiverCurrent,
    microphone_pcm_sha256: String,
    microphone_pcm_sample_population: usize,
    cold_pcm_rendering_only: bool,
    external_tts_called: bool,
    waveform_template_applied: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens4CultivatedReturnWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_rest_identity_sha256: String,
    successor_rest_identity_sha256: String,
    successor_body_identity_sha256: String,
    successor_wire_sha256: String,
    production_morphology_identity_sha256: String,
    room_witness_sha256: String,
    microphone_return_source_sha256: String,
    resident_receiver_current: NativeAcousticReceiverCurrent,
    membrane_crossed_exact_microphone_return: bool,
    resident_return_before_cultivation: ResidentMembraneInteriorReturn,
    cultivation: MembraneCultivationReceipt,
    returned_native_thread_population: usize,
    same_body_identity_changed_after_physical_return: bool,
    production_morphology_preserved_after_physical_return: bool,
    later_conduct_changed_after_physical_return: bool,
    exact_source_fibre_departed_before_rest: bool,
    source_access_after_commit: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens4VerificationWitness {
    successor_remounted_exactly: bool,
    complete_microphone_source_absent_from_successor_rest: bool,
    primary_production_reproduced_after_world_return: bool,
    held_out_production_reproduced_after_world_return: bool,
    primary_and_held_out_remain_distinct: bool,
    targeted_production_withdrawal_removed_owner: bool,
    targeted_production_restoration_exact: bool,
    production_morphology_identity_preserved: bool,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens4Return {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    predecessor_identity_sha256: String,
    acoustic_foundation_identity_sha256: String,
    cultivated_successor_identity_sha256: String,
    native_phase_extent: u32,
    native_causal_order_population: usize,
    distinct_native_waveforms_before_playback: bool,
    held_out_not_copied_from_cultivation: bool,
    source_detached_remount_reproduced_production: bool,
    room_impulse_lineages_distinct: bool,
    self_echo_lineages_distinct: bool,
    another_speaker_lineage_distinct: bool,
    overlap_returned: bool,
    interruption_returned: bool,
    exact_room_mode_population: usize,
    exact_self_return_grade_population: usize,
    separating_cross_mode_obstruction_population: usize,
    physical_return_changed_same_body_identity: bool,
    physical_return_changed_later_conduct: bool,
    targeted_production_ablation_removed_owner: bool,
    targeted_production_restoration_exact: bool,
    external_tts_called: bool,
    waveform_template_applied: bool,
    source_lookup_owned_output: bool,
    retained_foreign_runtime: bool,
    cpu_semantic_replay_after_device: bool,
    output_files: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    match env::var("SENS4_MODE").as_deref() {
        Ok("room") => room_phase(&root),
        Ok("return") => return_phase(&root),
        Ok("verify") => verify_phase(&root),
        Ok("grade") => grade_phase(&root),
        Ok("found") | Err(_) => foundation_phase(&root),
        Ok(other) => Err(format!("unknown SENS4_MODE {other}")),
    }
}

fn foundation_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    let primary = read_sens3_input(&root.join(SENS3).join("01-primary-open-world-tube.json"))?;
    let held_out = read_sens3_input(
        &root
            .join(SENS3)
            .join("02-precursor-ablated-open-world-tube.json"),
    )?;
    if primary.rested_identity_sha256 != held_out.rested_identity_sha256
        || primary.outward_port_population != held_out.outward_port_population
    {
        return Err(
            "the two native radiation sections do not share one rested boundary".to_owned(),
        );
    }
    let body = RecurrentGranularReturnedAffineEcologyRest::read(
        &fs::read(root.join(PREDECESSOR)).map_err(display)?,
    )
    .map_err(display)?;
    let predecessor_identity_sha256 = body.identity().to_owned();
    let (rest, cultivation) = AcousticProductRest::cultivate(body, &primary).map_err(display)?;
    eprintln!("sens4 foundation: source-neutral acoustic morphology cultivated");

    let step = Rat::new(BigInt::from(1), BigInt::from(SAMPLE_RATE));
    let primary_production = rest.radiate(&primary, step.clone()).map_err(display)?;
    let held_out_production = rest.radiate(&held_out, step).map_err(display)?;
    let exact_waveforms_distinct_before_playback =
        primary_production.exact_phase_current != held_out_production.exact_phase_current;
    if !exact_waveforms_distinct_before_playback {
        return Err("distinct native sections collapsed before the playback receiver".to_owned());
    }
    let primary_pcm = rest
        .project_pcm16(&primary_production, SAMPLE_RATE)
        .map_err(display)?;
    let held_out_pcm = rest
        .project_pcm16(&held_out_production, SAMPLE_RATE)
        .map_err(display)?;

    let rest_wire = rest.canonical_bytes().map_err(display)?;
    let remounted = AcousticProductRest::read(&rest_wire).map_err(display)?;
    let reproduced_primary = remounted
        .radiate(
            &primary,
            Rat::new(BigInt::from(1), BigInt::from(SAMPLE_RATE)),
        )
        .map_err(display)?;
    let reproduced_held_out = remounted
        .radiate(
            &held_out,
            Rat::new(BigInt::from(1), BigInt::from(SAMPLE_RATE)),
        )
        .map_err(display)?;
    let source_detached_remount_reproduced_primary = reproduced_primary == primary_production;
    let source_detached_remount_reproduced_held_out = reproduced_held_out == held_out_production;
    let acoustic_rest_identity_sha256 = remounted.identity().to_owned();
    let (body, withdrawn, withdrawal) = remounted.withdraw_production().map_err(display)?;
    let targeted_withdrawal_removed_production_owner =
        body.identity() == predecessor_identity_sha256;
    let (restored, restoration) =
        AcousticProductRest::restore_production(body, withdrawn).map_err(display)?;
    let targeted_restoration_exact = restored.identity() == acoustic_rest_identity_sha256;
    if !source_detached_remount_reproduced_primary
        || !source_detached_remount_reproduced_held_out
        || !targeted_withdrawal_removed_production_owner
        || !targeted_restoration_exact
    {
        return Err("the acoustic rest/remount or targeted inverse failed".to_owned());
    }

    fs::write(output.join("athena-acoustic-production.rest"), &rest_wire).map_err(display)?;
    write_json(&output.join("01-primary-native-radiation.json"), &primary)?;
    write_json(&output.join("02-held-out-native-radiation.json"), &held_out)?;
    write_json(
        &output.join("03-primary-exact-production.json"),
        &primary_production,
    )?;
    write_json(
        &output.join("04-held-out-exact-production.json"),
        &held_out_production,
    )?;
    write_json(
        &output.join("05-primary-pcm-reconstruction.json"),
        &primary_pcm,
    )?;
    write_json(
        &output.join("06-held-out-pcm-reconstruction.json"),
        &held_out_pcm,
    )?;
    fs::write(
        output.join("07-primary-native-radiation.wav"),
        primary_pcm.wav_bytes().map_err(display)?,
    )
    .map_err(display)?;
    fs::write(
        output.join("08-held-out-native-radiation.wav"),
        held_out_pcm.wav_bytes().map_err(display)?,
    )
    .map_err(display)?;

    let source_current_absent_from_morphology = !cultivation.source_current_retained_in_morphology;
    let waveform_template_absent = !cultivation.waveform_template_retained;
    let witness = Sens4FoundationWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_identity_sha256,
        acoustic_rest_identity_sha256,
        acoustic_rest_wire_sha256: sha256(&rest_wire),
        cultivation,
        primary_radiation_identity_sha256: primary.identity_sha256.clone(),
        held_out_radiation_identity_sha256: held_out.identity_sha256.clone(),
        primary_production_identity_sha256: primary_production.identity_sha256.clone(),
        held_out_production_identity_sha256: held_out_production.identity_sha256.clone(),
        primary_pcm_identity_sha256: primary_pcm.identity_sha256.clone(),
        held_out_pcm_identity_sha256: held_out_pcm.identity_sha256.clone(),
        phase_extent_derived_from_ports_and_quadratures: restored.production().phase_extent,
        causal_order_population: primary.orders.len(),
        exact_waveforms_distinct_before_playback,
        held_out_section_absent_from_cultivation: restored
            .production()
            .founding_radiation_identity_sha256
            != held_out.identity_sha256,
        source_current_absent_from_morphology,
        waveform_template_absent,
        source_detached_remount_reproduced_primary,
        source_detached_remount_reproduced_held_out,
        targeted_withdrawal_removed_production_owner,
        targeted_restoration_exact,
        withdrawal,
        restoration,
    };
    write_json(&output.join("09-foundation-witness.json"), &witness)?;
    eprintln!("sens4 foundation: two exact native waveforms and targeted inverse returned");
    Ok(())
}

fn room_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let production: NativeAcousticProductionSection = serde_json::from_slice(
        &fs::read(output.join("03-primary-exact-production.json")).map_err(display)?,
    )
    .map_err(display)?;
    production.validate().map_err(display)?;
    let pcm: life::native_intelligence::NativeAcousticPcm16Projection = serde_json::from_slice(
        &fs::read(output.join("05-primary-pcm-reconstruction.json")).map_err(display)?,
    )
    .map_err(display)?;
    pcm.validate().map_err(display)?;
    let (room_channels, room_rate, _room_bits) = read_integer_wav(Path::new(RIR))?;
    if room_rate != SAMPLE_RATE || room_channels.len() < 2 {
        return Err("the measured room does not share the native acoustic chart".to_owned());
    }
    let other_speaker = decode_mono_i32(Path::new(OTHER_SPEAKER), SAMPLE_RATE)?;
    let phase_extent =
        usize::try_from(production.exact_phase_current.phase_extent).map_err(display)?;
    let step = production.exact_phase_current.sample_step.clone();
    let room_digest = sha256(&fs::read(RIR).map_err(display)?);
    let speaker_digest = sha256(&fs::read(OTHER_SPEAKER).map_err(display)?);
    let room_receiver = WaveReceiverId(stable_u64(b"sens4/native-acoustic-radiation"));
    let microphone_receiver = WaveReceiverId(stable_u64(b"sens4/physical-microphone-return"));
    let interaction = WaveInteractionId(stable_u64(b"sens4/measured-room-transport"));

    let mut response_sections = Vec::with_capacity(room_channels.len());
    let mut spectra = Vec::with_capacity(room_channels.len());
    for (channel, samples) in room_channels.iter().enumerate() {
        let response = ExactPhaseCurrentSection::from_i32(
            PhaseCurrentReceiverId(stable_u64(format!("sens4/room/{channel}").as_bytes())),
            PhaseCurrentLineageId(stable_u64(
                format!("{room_digest}/room-channel/{channel}").as_bytes(),
            )),
            Rat::from_integer(BigInt::from(0)),
            step.clone(),
            phase_extent,
            samples,
        )
        .map_err(display)?;
        spectra.push(
            receive_phase_transport_spectrum(
                &production.exact_phase_current,
                &response,
                PhaseCurrentReceiverId(stable_u64(format!("sens4/self-echo/{channel}").as_bytes())),
                PhaseCurrentLineageId(stable_u64(
                    format!("{room_digest}/self-echo/{channel}").as_bytes(),
                )),
            )
            .map_err(display)?,
        );
        response_sections.push(response);
    }
    eprintln!("sens4 room: exact phase-and-carry room spectra returned");

    let spec = WavePropagationSpec::new(
        [
            WaveReceiverSpec {
                id: room_receiver,
                name: "native acoustic radiation current".to_owned(),
                channels: 1,
            },
            WaveReceiverSpec {
                id: microphone_receiver,
                name: "physical microphone return current".to_owned(),
                channels: 1,
            },
        ],
        [WaveInteractionSpec {
            id: interaction,
            name: "measured Aula Carolina room transport".to_owned(),
            source: room_receiver,
            target: microphone_receiver,
        }],
    )
    .map_err(display)?;
    let workers = NonZeroUsize::new(
        std::thread::available_parallelism()
            .map_err(display)?
            .get()
            .min(8),
    )
    .ok_or_else(|| "the room apparatus has no CPU worker".to_owned())?;
    let law =
        ExactWavePropagationLaw::new(spec, CpuExecutor::multicore(workers)).map_err(display)?;
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    let coarse_step = &step * BigInt::from(phase_extent);
    let impulse = exact_wave_section(
        room_receiver,
        stable_u64(b"sens4/room-impulse"),
        coarse_step.clone(),
        vec![BigInt::from(1)],
    )?;
    let native_coarse = exact_wave_section(
        room_receiver,
        stable_u64(production.identity_sha256.as_bytes()),
        coarse_step.clone(),
        production.exact_phase_current.integrated_cells(),
    )?;
    let mut transitions = Vec::new();
    let mut response_kernels = Vec::with_capacity(response_sections.len());
    let mut event = 1_u64;
    for response in &response_sections {
        let kernel = response.integrated_cells();
        let target = exact_wave_section(
            microphone_receiver,
            response.lineage.0,
            coarse_step.clone(),
            kernel.clone(),
        )?;
        transitions.push(
            world
                .receive(&WavePropagationEvent::Condition(WaveConditioningEvent {
                    event: EventId(event),
                    interaction,
                    source: impulse.clone(),
                    target_return: target,
                }))
                .map_err(display)?,
        );
        response_kernels.push(kernel);
        event += 1;
    }
    let mut predictions = Vec::with_capacity(response_sections.len());
    for _ in &response_sections {
        let receipt = world
            .receive(&WavePropagationEvent::Generate(WaveGenerationEvent {
                event: EventId(event),
                interaction,
                source: native_coarse.clone(),
            }))
            .map_err(display)?;
        let WavePropagationRadiation::Generated(generated) = &receipt.radiation[0] else {
            return Err("the room owner did not generate a native self-echo".to_owned());
        };
        predictions.push(generated.prediction);
        transitions.push(receipt);
        event += 1;
    }
    let generated_before_return_population = predictions.len();
    let mut exact_return_grade_population = 0_usize;
    let mut obstructed_return_grade_population = 0_usize;
    for (prediction, kernel) in predictions.into_iter().zip(&response_kernels) {
        let exact_target =
            convolve_exact(&production.exact_phase_current.integrated_cells(), kernel);
        let receipt = world
            .receive(&WavePropagationEvent::Return(WavePredictionReturnEvent {
                event: EventId(event),
                prediction,
                target_return: exact_wave_section(
                    microphone_receiver,
                    stable_u64(format!("sens4/returned/{event}").as_bytes()),
                    coarse_step.clone(),
                    exact_target,
                )?,
                condition_after_grade: false,
            }))
            .map_err(display)?;
        let WavePropagationRadiation::Returned(returned) = &receipt.radiation[0] else {
            return Err("the room owner did not grade its physical return".to_owned());
        };
        for grade in &returned.grades {
            if grade.exact {
                exact_return_grade_population += 1;
            } else {
                obstructed_return_grade_population += 1;
            }
        }
        transitions.push(receipt);
        event += 1;
    }
    let exact_wave_mode_population = world
        .standing()
        .modes(interaction)
        .ok_or_else(|| "the measured room has no founded transport mode".to_owned())?
        .len();
    let transition_bytes = serde_json::to_vec_pretty(&transitions).map_err(display)?;
    fs::write(
        output.join("10-exact-room-propagation.json"),
        &transition_bytes,
    )
    .map_err(display)?;
    write_json(&output.join("11-exact-room-phase-spectra.json"), &spectra)?;

    let native_values = pcm
        .samples
        .iter()
        .copied()
        .map(i32::from)
        .collect::<Vec<_>>();
    let left_echo = convolve_pcm(&native_values, &room_channels[0]);
    let right_echo = convolve_pcm(&native_values, &room_channels[1]);
    let speaker_begin = phase_extent;
    let microphone = mix_microphone(&left_echo, &right_echo, &other_speaker, speaker_begin);
    let microphone_wav = render_i64_pcm16(&microphone, SAMPLE_RATE)?;
    fs::write(
        output.join("12-full-duplex-microphone-return.wav"),
        &microphone_wav,
    )
    .map_err(display)?;

    let native_sum = production
        .exact_phase_current
        .flat_values()
        .into_iter()
        .fold(BigInt::from(0), |sum, value| sum + value);
    let left_response_sum = room_channels[0]
        .iter()
        .fold(BigInt::from(0), |sum, value| sum + BigInt::from(*value));
    let right_response_sum = room_channels[1]
        .iter()
        .fold(BigInt::from(0), |sum, value| sum + BigInt::from(*value));
    let other_sum = other_speaker
        .iter()
        .fold(BigInt::from(0), |sum, value| sum + BigInt::from(*value));
    let denominator = BigInt::from(production.common_denominator.clone());
    let exact_self_echo_left_current =
        Rat::new(&native_sum * left_response_sum, denominator.clone());
    let exact_self_echo_right_current =
        Rat::new(&native_sum * right_response_sum, denominator.clone());
    let exact_other_speaker_current = Rat::from_integer(other_sum);
    let exact_microphone_return = ExactComplexWaveCurrent::new(
        &exact_self_echo_left_current + &exact_other_speaker_current,
        &exact_self_echo_right_current + &exact_other_speaker_current,
    );
    let other_speaker_section = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(stable_u64(b"sens4/other-speaker")),
        PhaseCurrentLineageId(stable_u64(speaker_digest.as_bytes())),
        Rat::from_integer(BigInt::from(0)),
        step.clone(),
        phase_extent,
        &other_speaker,
    )
    .map_err(display)?;
    let resident_receiver_current = NativeAcousticReceiverCurrent::found(
        exact_microphone_return.clone(),
        &spectra,
        &other_speaker_section,
    )
    .map_err(display)?;
    let native_end = production.exact_phase_current.raw_extent();
    let echo_end = left_echo.len().max(right_echo.len());
    let speaker_end = speaker_begin + other_speaker.len();
    let overlap_end = native_end.min(speaker_end);
    let room_impulse_intervals = response_sections
        .iter()
        .map(|section| ExactAcousticInterval {
            lineage: section.lineage,
            begin_sample: 0,
            end_sample: u64::try_from(section.raw_extent()).unwrap_or(u64::MAX),
        })
        .collect::<Vec<_>>();
    let self_echo_intervals = spectra
        .iter()
        .map(|spectrum| ExactAcousticInterval {
            lineage: spectrum.target_lineage,
            begin_sample: 0,
            end_sample: u64::try_from(echo_end).unwrap_or(u64::MAX),
        })
        .collect::<Vec<_>>();
    let other_lineage = PhaseCurrentLineageId(stable_u64(speaker_digest.as_bytes()));
    let witness = Sens4RoomWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        primary_production_identity_sha256: production.identity_sha256,
        room_response_path: RIR.to_owned(),
        room_response_sha256: room_digest,
        other_speaker_path: OTHER_SPEAKER.to_owned(),
        other_speaker_sha256: speaker_digest,
        sample_rate: SAMPLE_RATE,
        exact_sample_step: step,
        native_phase_extent: u32::try_from(phase_extent).map_err(display)?,
        native_sample_population: native_end,
        room_channel_population: room_channels.len(),
        room_sample_population_per_channel: room_channels[0].len(),
        other_speaker_sample_population: other_speaker.len(),
        exact_phase_spectrum_sha256: spectra
            .iter()
            .map(|spectrum| {
                serde_json::to_vec(spectrum)
                    .map(|bytes| sha256(&bytes))
                    .map_err(display)
            })
            .collect::<Result<Vec<_>, _>>()?,
        exact_wave_transition_receipts_sha256: sha256(&transition_bytes),
        exact_wave_mode_population,
        generated_before_return_population,
        exact_return_grade_population,
        obstructed_return_grade_population,
        room_impulse_intervals,
        self_echo_intervals,
        other_speaker_interval: ExactAcousticInterval {
            lineage: other_lineage,
            begin_sample: u64::try_from(speaker_begin).map_err(display)?,
            end_sample: u64::try_from(speaker_end).map_err(display)?,
        },
        overlap_interval: ExactAcousticInterval {
            lineage: PhaseCurrentLineageId(stable_u64(b"sens4/full-duplex-overlap")),
            begin_sample: u64::try_from(speaker_begin).map_err(display)?,
            end_sample: u64::try_from(overlap_end).map_err(display)?,
        },
        interruption_interval: ExactAcousticInterval {
            lineage: PhaseCurrentLineageId(stable_u64(b"sens4/strict-interruption")),
            begin_sample: u64::try_from(speaker_begin).map_err(display)?,
            end_sample: u64::try_from(native_end).map_err(display)?,
        },
        room_impulse_lineages_distinct: response_sections[0].lineage
            != response_sections[1].lineage,
        self_echo_lineages_distinct: spectra[0].target_lineage != spectra[1].target_lineage,
        other_speaker_lineage_distinct: response_sections
            .iter()
            .all(|response| response.lineage != other_lineage)
            && spectra
                .iter()
                .all(|spectrum| spectrum.target_lineage != other_lineage),
        overlap_present: speaker_begin < overlap_end,
        strict_interruption_present: speaker_begin < native_end,
        exact_self_echo_left_current,
        exact_self_echo_right_current,
        exact_other_speaker_current,
        exact_microphone_return,
        resident_receiver_current,
        microphone_pcm_sha256: sha256(&microphone_wav),
        microphone_pcm_sample_population: microphone.len(),
        cold_pcm_rendering_only: true,
        external_tts_called: false,
        waveform_template_applied: false,
    };
    if witness.exact_return_grade_population < response_sections.len()
        || witness.obstructed_return_grade_population < response_sections.len()
        || !witness.room_impulse_lineages_distinct
        || !witness.self_echo_lineages_distinct
        || !witness.other_speaker_lineage_distinct
        || !witness.overlap_present
        || !witness.strict_interruption_present
    {
        return Err("the exact full-duplex room receiver did not close".to_owned());
    }
    write_json(&output.join("13-full-duplex-room-witness.json"), &witness)?;
    eprintln!("sens4 room: room impulse, self-echo, speaker, overlap, and interruption returned");
    Ok(())
}

fn return_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let room_bytes = fs::read(output.join("13-full-duplex-room-witness.json")).map_err(display)?;
    let room: Sens4RoomWitness = serde_json::from_slice(&room_bytes).map_err(display)?;
    let rest = AcousticProductRest::read(
        &fs::read(output.join("athena-acoustic-production.rest")).map_err(display)?,
    )
    .map_err(display)?;
    let predecessor_rest_identity_sha256 = rest.identity().to_owned();
    let production_morphology_identity_sha256 = rest.production().identity_sha256.clone();
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let (left, shared, _unrelated) = receiver_cells(rest.membrane_affine_cells())?;
    let exact_return_payload = serde_json::to_vec(&(
        "sens4/full-duplex-physical-microphone-return",
        &room.room_response_sha256,
        &room.other_speaker_sha256,
        &room.exact_microphone_return,
        &room.room_impulse_intervals,
        &room.self_echo_intervals,
        &room.other_speaker_interval,
        &room.overlap_interval,
        &room.interruption_interval,
        &room.resident_receiver_current,
    ))
    .map_err(display)?;
    let microphone_return_source_sha256 = sha256(&exact_return_payload);
    let occurrence = AddressedMaterialOccurrence::found(
        "sens4/acoustic/full-duplex-microphone-return",
        &exact_return_payload,
        Some(format!(
            "sens4/native-radiation/{}",
            room.primary_production_identity_sha256
        )),
        vec!["cold physical microphone delivery".to_owned()],
        vec!["later acoustic world consequences remain open".to_owned()],
    )
    .map_err(display)?;
    let expected_occurrence = occurrence.clone();
    let source_fibre = occurrence.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(source_fibre.address().event_projection.0);
    let dimension = BaseUnits::declare(["physical-acoustic-return-current"])
        .map_err(display)?
        .unit("physical-acoustic-return-current")
        .map_err(display)?;
    let injected = room.resident_receiver_current.resident_current.clone();
    let mut membrane = NativeCausalMembrane::mount(rest)
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
        .map_err(|failure| format!("the physical microphone binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(initial_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the physical microphone return did not cross the Athena membrane".to_owned());
    };
    let recovered = initial_return
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|_| "the complete microphone source fibre did not return".to_owned())?;
    let membrane_crossed_exact_microphone_return = recovered == expected_occurrence;
    let resident_return = membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    eprintln!("sens4 return: physical full-duplex occurrence crossed resident Athena conduct");
    let world_payload = serde_json::to_vec(&(
        "sens4/returned-room-world-consequence",
        &microphone_return_source_sha256,
        &resident_return.native_radiation,
        &resident_return.returned_radiation,
        &resident_return.family_overlaps,
    ))
    .map_err(display)?;
    let world_source = AddressedMaterialOccurrence::found(
        "sens4/world/returned-room-consequence",
        &world_payload,
        Some("sens4/acoustic/full-duplex-microphone-return".to_owned()),
        vec!["cold returned-room delivery".to_owned()],
        vec!["later physical acoustic consequences remain open".to_owned()],
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
        .map_err(|failure| format!("the room world-return binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(world_return) =
        membrane.receive_occurrence(later).map_err(display)?
    else {
        return Err("the room world consequence did not return".to_owned());
    };
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_return.clone())
        .map_err(display)?;
    let (rest, detached) = staged.detach().map_err(display)?;
    let detached_bytes = detached.canonical_bytes().map_err(display)?;
    fs::write(
        output.join("14-detached-physical-room-return.json"),
        &detached_bytes,
    )
    .map_err(display)?;
    let (successor, cultivation, successor_wire) =
        detached.commit_restable(rest).map_err(display)?;
    let successor_rest_identity_sha256 = successor.identity().to_owned();
    let successor_body_identity_sha256 = successor.body().identity().to_owned();
    let same_body_identity_changed_after_physical_return =
        successor_rest_identity_sha256 != predecessor_rest_identity_sha256;
    let production_morphology_preserved_after_physical_return =
        successor.production().identity_sha256 == production_morphology_identity_sha256;
    let returned_native_thread_population =
        successor.body().body().body().returned_deposits().len();
    let mut later_membrane = NativeCausalMembrane::mount(successor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let later_conduct = later_membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    let later_conduct_changed_after_physical_return = later_conduct != resident_return;
    let successor = later_membrane.into_rest();
    if successor.identity() != successor_rest_identity_sha256
        || !same_body_identity_changed_after_physical_return
        || !production_morphology_preserved_after_physical_return
        || !later_conduct_changed_after_physical_return
        || !membrane_crossed_exact_microphone_return
    {
        return Err("the physical room return did not cultivate the same Athena body".to_owned());
    }
    let witness = Sens4CultivatedReturnWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_rest_identity_sha256,
        successor_rest_identity_sha256,
        successor_body_identity_sha256,
        successor_wire_sha256: sha256(&successor_wire),
        production_morphology_identity_sha256,
        room_witness_sha256: sha256(&room_bytes),
        microphone_return_source_sha256,
        resident_receiver_current: room.resident_receiver_current,
        membrane_crossed_exact_microphone_return,
        resident_return_before_cultivation: resident_return,
        returned_native_thread_population,
        same_body_identity_changed_after_physical_return,
        production_morphology_preserved_after_physical_return,
        later_conduct_changed_after_physical_return,
        exact_source_fibre_departed_before_rest: cultivation
            .exact_source_fibre_departed_before_rest,
        source_access_after_commit: cultivation.source_access_after_commit,
        cultivation,
    };
    fs::write(
        output.join("athena-acoustic-room-cultivated.rest"),
        successor_wire,
    )
    .map_err(display)?;
    write_json(
        &output.join("15-cultivated-room-return-witness.json"),
        &witness,
    )?;
    eprintln!("sens4 return: physical return changed the same body and its later conduct");
    Ok(())
}

fn verify_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let foundation: Sens4FoundationWitness = serde_json::from_slice(
        &fs::read(output.join("09-foundation-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let cultivated: Sens4CultivatedReturnWitness = serde_json::from_slice(
        &fs::read(output.join("15-cultivated-room-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let successor_wire =
        fs::read(output.join("athena-acoustic-room-cultivated.rest")).map_err(display)?;
    let successor = AcousticProductRest::read(&successor_wire).map_err(display)?;
    let successor_remounted_exactly = successor.identity()
        == cultivated.successor_rest_identity_sha256
        && sha256(&successor_wire) == cultivated.successor_wire_sha256;
    let room_source = fs::read(output.join("13-full-duplex-room-witness.json")).map_err(display)?;
    let complete_microphone_source_absent_from_successor_rest = !successor_wire
        .windows(room_source.len())
        .any(|window| window == room_source.as_slice())
        && !successor_wire
            .windows(cultivated.microphone_return_source_sha256.len())
            .any(|window| window == cultivated.microphone_return_source_sha256.as_bytes());
    let primary = NativeAcousticRadiationInput::read(
        &fs::read(output.join("01-primary-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held_out = NativeAcousticRadiationInput::read(
        &fs::read(output.join("02-held-out-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let step = Rat::new(BigInt::from(1), BigInt::from(SAMPLE_RATE));
    let primary_production = successor.radiate(&primary, step.clone()).map_err(display)?;
    let held_out_production = successor.radiate(&held_out, step).map_err(display)?;
    let primary_production_reproduced_after_world_return =
        primary_production.identity_sha256 == foundation.primary_production_identity_sha256;
    let held_out_production_reproduced_after_world_return =
        held_out_production.identity_sha256 == foundation.held_out_production_identity_sha256;
    let primary_and_held_out_remain_distinct = primary_production != held_out_production;
    let morphology = successor.production().identity_sha256.clone();
    let successor_identity = successor.identity().to_owned();
    let (body, withdrawn, _withdrawal) = successor.withdraw_production().map_err(display)?;
    let targeted_production_withdrawal_removed_owner = body.identity() != successor_identity
        && body.identity() == cultivated.successor_body_identity_sha256;
    let (restored, _restoration) =
        AcousticProductRest::restore_production(body, withdrawn).map_err(display)?;
    let targeted_production_restoration_exact = restored.identity() == successor_identity;
    let production_morphology_identity_preserved = restored.production().identity_sha256
        == morphology
        && morphology == cultivated.production_morphology_identity_sha256;
    let witness = Sens4VerificationWitness {
        successor_remounted_exactly,
        complete_microphone_source_absent_from_successor_rest,
        primary_production_reproduced_after_world_return,
        held_out_production_reproduced_after_world_return,
        primary_and_held_out_remain_distinct,
        targeted_production_withdrawal_removed_owner,
        targeted_production_restoration_exact,
        production_morphology_identity_preserved,
    };
    if !witness.successor_remounted_exactly
        || !witness.complete_microphone_source_absent_from_successor_rest
        || !witness.primary_production_reproduced_after_world_return
        || !witness.held_out_production_reproduced_after_world_return
        || !witness.primary_and_held_out_remain_distinct
        || !witness.targeted_production_withdrawal_removed_owner
        || !witness.targeted_production_restoration_exact
        || !witness.production_morphology_identity_preserved
    {
        return Err("the source-detached SENS4 remount or targeted inverse failed".to_owned());
    }
    write_json(
        &output.join("16-source-detached-verification.json"),
        &witness,
    )?;
    eprintln!("sens4 verify: source-detached conduct and targeted production inverse passed");
    Ok(())
}

fn grade_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let foundation: Sens4FoundationWitness = serde_json::from_slice(
        &fs::read(output.join("09-foundation-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let room: Sens4RoomWitness = serde_json::from_slice(
        &fs::read(output.join("13-full-duplex-room-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let cultivated: Sens4CultivatedReturnWitness = serde_json::from_slice(
        &fs::read(output.join("15-cultivated-room-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let verified: Sens4VerificationWitness = serde_json::from_slice(
        &fs::read(output.join("16-source-detached-verification.json")).map_err(display)?,
    )
    .map_err(display)?;
    let result = Sens4Return {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        predecessor_identity_sha256: foundation.predecessor_identity_sha256,
        acoustic_foundation_identity_sha256: foundation.acoustic_rest_identity_sha256,
        cultivated_successor_identity_sha256: cultivated.successor_rest_identity_sha256,
        native_phase_extent: room.native_phase_extent,
        native_causal_order_population: foundation.causal_order_population,
        distinct_native_waveforms_before_playback: foundation
            .exact_waveforms_distinct_before_playback,
        held_out_not_copied_from_cultivation: foundation.held_out_section_absent_from_cultivation
            && foundation.source_current_absent_from_morphology
            && foundation.waveform_template_absent,
        source_detached_remount_reproduced_production: foundation
            .source_detached_remount_reproduced_primary
            && foundation.source_detached_remount_reproduced_held_out
            && verified.primary_production_reproduced_after_world_return
            && verified.held_out_production_reproduced_after_world_return,
        room_impulse_lineages_distinct: room.room_impulse_lineages_distinct,
        self_echo_lineages_distinct: room.self_echo_lineages_distinct,
        another_speaker_lineage_distinct: room.other_speaker_lineage_distinct,
        overlap_returned: room.overlap_present,
        interruption_returned: room.strict_interruption_present,
        exact_room_mode_population: room.exact_wave_mode_population,
        exact_self_return_grade_population: room.exact_return_grade_population,
        separating_cross_mode_obstruction_population: room.obstructed_return_grade_population,
        physical_return_changed_same_body_identity: cultivated
            .same_body_identity_changed_after_physical_return,
        physical_return_changed_later_conduct: cultivated
            .later_conduct_changed_after_physical_return,
        targeted_production_ablation_removed_owner: foundation
            .targeted_withdrawal_removed_production_owner
            && verified.targeted_production_withdrawal_removed_owner,
        targeted_production_restoration_exact: foundation.targeted_restoration_exact
            && verified.targeted_production_restoration_exact,
        external_tts_called: room.external_tts_called,
        waveform_template_applied: room.waveform_template_applied,
        source_lookup_owned_output: false,
        retained_foreign_runtime: false,
        cpu_semantic_replay_after_device: cultivated
            .resident_return_before_cultivation
            .cpu_semantic_replay_after_device,
        output_files: vec![
            "07-primary-native-radiation.wav".to_owned(),
            "08-held-out-native-radiation.wav".to_owned(),
            "10-exact-room-propagation.json".to_owned(),
            "11-exact-room-phase-spectra.json".to_owned(),
            "12-full-duplex-microphone-return.wav".to_owned(),
            "athena-acoustic-production.rest".to_owned(),
            "athena-acoustic-room-cultivated.rest".to_owned(),
        ],
    };
    if !result.distinct_native_waveforms_before_playback
        || !result.held_out_not_copied_from_cultivation
        || !result.source_detached_remount_reproduced_production
        || !result.room_impulse_lineages_distinct
        || !result.self_echo_lineages_distinct
        || !result.another_speaker_lineage_distinct
        || !result.overlap_returned
        || !result.interruption_returned
        || !result.physical_return_changed_same_body_identity
        || !result.physical_return_changed_later_conduct
        || !result.targeted_production_ablation_removed_owner
        || !result.targeted_production_restoration_exact
        || result.external_tts_called
        || result.waveform_template_applied
        || result.source_lookup_owned_output
        || result.retained_foreign_runtime
        || result.cpu_semantic_replay_after_device
    {
        return Err("the SENS4 qualitative receiver did not close".to_owned());
    }
    write_json(&output.join("00-sens4-return.json"), &result)?;
    Ok(())
}

fn read_sens3_input(path: &Path) -> Result<NativeAcousticRadiationInput, String> {
    let stored: StoredSens3Probe =
        serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)?;
    let mut current_returns = stored.native_return.current_returns.into_iter();
    let returned = current_returns
        .next()
        .ok_or_else(|| "the stored SENS3 receipt has no returned current".to_owned())?;
    if current_returns.next().is_some() {
        return Err("the SENS3 acoustic source face is not singular".to_owned());
    }
    NativeAcousticRadiationInput::found_returned(
        stored.native_return.rested_identity_sha256,
        stored.native_return.identity_sha256,
        returned.source_section,
        stored.native_return.outward_port_population,
        returned
            .orders
            .into_iter()
            .map(|order| NativeAcousticRadiationOrder {
                causal_order: order.causal_order,
                outward_port_returns: order.outward_port_returns,
            })
            .collect(),
        returned.terminal,
    )
    .map_err(display)
}

fn exact_wave_section(
    receiver: WaveReceiverId,
    lineage: u64,
    step: Rat,
    values: Vec<BigInt>,
) -> Result<ExactWaveSection, String> {
    ExactWaveSection::new(
        receiver,
        WaveLineageId(lineage),
        Rat::from_integer(BigInt::from(0)),
        step,
        values
            .into_iter()
            .map(|value| vec![Rat::from_integer(value)])
            .collect(),
    )
    .map_err(display)
}

fn convolve_exact(source: &[BigInt], response: &[BigInt]) -> Vec<BigInt> {
    let mut output = vec![BigInt::from(0); source.len() + response.len() - 1];
    for (source_ordinal, source_current) in source.iter().enumerate() {
        if source_current == &BigInt::from(0) {
            continue;
        }
        for (delay, response_current) in response.iter().enumerate() {
            if response_current != &BigInt::from(0) {
                output[source_ordinal + delay] += source_current * response_current;
            }
        }
    }
    output
}

fn read_integer_wav(path: &Path) -> Result<(Vec<Vec<i32>>, u32, u16), String> {
    let reader = hound::WavReader::open(path).map_err(display)?;
    let spec = reader.spec();
    if spec.sample_format != hound::SampleFormat::Int || spec.channels == 0 {
        return Err(format!("{} is not integer PCM", path.display()));
    }
    let mut channels = vec![Vec::new(); usize::from(spec.channels)];
    let channel_count = channels.len();
    for (ordinal, sample) in reader.into_samples::<i32>().enumerate() {
        channels[ordinal % channel_count].push(sample.map_err(display)?);
    }
    Ok((channels, spec.sample_rate, spec.bits_per_sample))
}

fn decode_mono_i32(path: &Path, sample_rate: u32) -> Result<Vec<i32>, String> {
    let decoded = Command::new("ffmpeg")
        .args(["-v", "error", "-i"])
        .arg(path)
        .args([
            "-map",
            "0:a:0",
            "-ac",
            "1",
            "-ar",
            &sample_rate.to_string(),
            "-f",
            "s16le",
            "-",
        ])
        .output()
        .map_err(display)?;
    if !decoded.status.success() || decoded.stdout.len() % 2 != 0 {
        return Err(format!(
            "the other-speaker decode refused: {}",
            String::from_utf8_lossy(&decoded.stderr)
        ));
    }
    Ok(decoded
        .stdout
        .chunks_exact(2)
        .map(|pair| i32::from(i16::from_le_bytes([pair[0], pair[1]])))
        .collect())
}

fn convolve_pcm(source: &[i32], response: &[i32]) -> Vec<i64> {
    let mut output = vec![0_i64; source.len() + response.len() - 1];
    for (source_ordinal, source_current) in source.iter().enumerate() {
        if *source_current == 0 {
            continue;
        }
        for (delay, response_current) in response.iter().enumerate() {
            if *response_current != 0 {
                output[source_ordinal + delay] +=
                    i64::from(*source_current) * i64::from(*response_current);
            }
        }
    }
    output
}

fn mix_microphone(
    left_echo: &[i64],
    right_echo: &[i64],
    other_speaker: &[i32],
    speaker_begin: usize,
) -> Vec<i64> {
    let extent = left_echo
        .len()
        .max(right_echo.len())
        .max(speaker_begin + other_speaker.len());
    let mut output = vec![0_i64; extent];
    for ordinal in 0..left_echo.len().max(right_echo.len()) {
        let left = left_echo.get(ordinal).copied().unwrap_or(0);
        let right = right_echo.get(ordinal).copied().unwrap_or(0);
        output[ordinal] = left / 2 + right / 2;
    }
    for (ordinal, sample) in other_speaker.iter().enumerate() {
        output[speaker_begin + ordinal] += i64::from(*sample);
    }
    output
}

fn render_i64_pcm16(samples: &[i64], sample_rate: u32) -> Result<Vec<u8>, String> {
    let maximum = samples
        .iter()
        .map(|sample| sample.unsigned_abs())
        .max()
        .unwrap_or(0);
    let divisor = maximum.div_ceil(i16::MAX as u64).max(1);
    let specification = hound::WavSpec {
        channels: 1,
        sample_rate,
        bits_per_sample: 16,
        sample_format: hound::SampleFormat::Int,
    };
    let mut bytes = Vec::new();
    {
        let cursor = std::io::Cursor::new(&mut bytes);
        let mut writer = hound::WavWriter::new(cursor, specification).map_err(display)?;
        for sample in samples {
            let scaled = *sample / i64::try_from(divisor).map_err(display)?;
            writer
                .write_sample(i16::try_from(scaled).map_err(display)?)
                .map_err(display)?;
        }
        writer.finalize().map_err(display)?;
    }
    Ok(bytes)
}

fn stable_u64(bytes: &[u8]) -> u64 {
    let digest = Sha256::digest(bytes);
    u64::from_le_bytes(
        digest[..8]
            .try_into()
            .expect("sha256 prefix is eight bytes"),
    )
}

fn continuing_native_address(
    rest: &impl MembraneStanding,
) -> Result<(life::native_intelligence::NativeSectionAddress, ReceiverId), String> {
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
    Err("the acoustic Athena body has no continuing native address".to_owned())
}

fn receiver_cells(
    cells: &[life::native_intelligence::LaboratoryCellAffineSection],
) -> Result<(String, String, String), String> {
    let left = cells
        .first()
        .ok_or_else(|| "the affine organ has no cells".to_owned())?;
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
        .ok_or_else(|| "the affine organ has no shared-support cell".to_owned())?;
    let unrelated = cells
        .iter()
        .rev()
        .find(|cell| cell.cell_address != left.cell_address)
        .ok_or_else(|| "the affine organ has no sibling cell".to_owned())?;
    Ok((
        left.cell_address.clone(),
        shared.cell_address.clone(),
        unrelated.cell_address.clone(),
    ))
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
