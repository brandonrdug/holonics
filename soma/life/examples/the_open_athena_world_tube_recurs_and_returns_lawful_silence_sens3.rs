//! Focused SENS3 receiver over the exact SENS2 successor.
//!
//! One real GRID occurrence is reconstructed under two packet covers, charted through its exact
//! acoustic/optical clocks, and carried through the standing resident factor-current recurrence.
//! Source cells and packet cuts remain exterior lineage. The host supplies neither a native cell
//! nor a response extent; exact dynamic rest or a repeated complete current front ends recurrence.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{quantity::BaseUnits, ExactComplexWaveCurrent};
use life::{
    addressed_span::{AddressedMemorySpan, CompleteAddressedMemorySpan, MemorySpanFragment},
    athena_native::{
        AthenaCausalMembrane, ExactMembraneChartPassage, ExteriorOccurrenceTransducer,
        NativeOpenWorldTubeReceipt, RecurrentGranularReturnedAffineAthenaRest,
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
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_membrane::ReceiverChartIdentity;

const PREDECESSOR: &str = concat!(
    "output/the_synchronized_sensory_world_tube_cultivates_one_athena_body_sens2/",
    "athena-synchronized-sensory.rest"
);
const GRID: &str =
    "/home/b/Workspaces/laboratory/runs/information-flow-datasets/source/GRID/s1/bbaf2n.mpg";
const OUTPUT: &str = "output/the_open_athena_world_tube_recurs_and_returns_lawful_silence_sens3";

const AUDIO: SynchronizedReceiverId = SynchronizedReceiverId(0x4155_4449_4f);
const VIDEO: SynchronizedReceiverId = SynchronizedReceiverId(0x5649_4445_4f);
const AUDIO_HZ: i64 = 8_000;
const VIDEO_HZ: i64 = 50;
const FRAME_PIXELS: usize = 90 * 72;
const AUDIO_CELL_COUNT: usize = 5;
const VIDEO_FRAME_COUNT: usize = 4;
const SAMPLES_PER_FRAME: usize = (AUDIO_HZ / VIDEO_HZ) as usize;

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens3Probe {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    precursor_ablated: bool,
    source_sha256: String,
    incidence_sha256: String,
    whole_fragment_population: u64,
    rechunked_fragment_population: u64,
    packetization_natural_before_native_contact: bool,
    synchronized_contact_population: usize,
    source_cell_population: usize,
    ignored_source_cell_population: usize,
    overlapping_contact_population: usize,
    interruption_contact_population: usize,
    presented_section: ExactComplexWaveCurrent,
    presented_current: ExactComplexWaveCurrent,
    native_return: NativeOpenWorldTubeReceipt,
    exact_source_recovered: bool,
    rested_identity_returned_unchanged: bool,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens3Return {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    primary_return_identity_sha256: String,
    ablated_return_identity_sha256: String,
    packetization_naturality_returned: bool,
    ignored_interval_population: usize,
    overlap_interval_population: usize,
    interruption_interval_population: usize,
    internally_retained_new_ray_population: usize,
    immediately_radiated_port_population: usize,
    delayed_radiated_port_population: usize,
    persistent_lawful_silence_port_population: usize,
    precursor_attributable_later_response_population: usize,
    precursor_ablation_preserved_native_topology: bool,
    exact_dynamic_condensation_returned: bool,
    exact_source_fibres_returned: bool,
    same_rest_returned_unchanged: bool,
    every_generator_descent_returned_on_card: bool,
    word_or_clause_renderer_ran: bool,
    wake_word_or_vad_gate_present: bool,
    timer_or_maximum_turn_present: bool,
    host_selected_native_contact: bool,
    invariant_transport_reuploaded: bool,
    cpu_semantic_replay_after_device: bool,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    if env::var_os("SENS3_GRADE").is_some() {
        return grade_phase(&root);
    }
    let precursor_ablated = env::var_os("SENS3_ABLATE_PRECURSOR").is_some();
    let encoded = fs::read(GRID).map_err(display)?;
    let whole = assemble(&encoded, &[encoded.len()])?;
    let rechunked = assemble(&encoded, &[13, 4096, 73, 1537, 29, 8003, 509])?;
    let packetization_natural_before_native_contact = whole.body == rechunked.body
        && whole.source_sha256 == rechunked.source_sha256
        && whole.source_octets == rechunked.source_octets;
    if !packetization_natural_before_native_contact {
        return Err("packet covers changed the exact GRID source before native contact".to_owned());
    }

    let audio = decode_audio(Path::new(GRID))?;
    let video = decode_video(Path::new(GRID))?;
    if audio.len() < AUDIO_CELL_COUNT * SAMPLES_PER_FRAME
        || video.len() != VIDEO_FRAME_COUNT * FRAME_PIXELS
    {
        return Err("the bounded GRID decode did not return the declared world tube".to_owned());
    }
    let synchronized = synchronized_occurrence(&audio, &video, precursor_ablated)?;
    let contacts = SynchronizedOccurrenceChart::new()
        .contacts(&synchronized)
        .map_err(display)?;
    let source_cell_population = synchronized
        .sections
        .iter()
        .map(|section| section.cells.len())
        .sum::<usize>();
    let contacted = contacts
        .iter()
        .flat_map(|contact| contact.left_cells.iter().chain(&contact.right_cells))
        .copied()
        .collect::<BTreeSet<_>>();
    let ignored_source_cell_population = source_cell_population - contacted.len();
    let overlapping_contact_population = contacts.len();
    let interruption_contact_population = interruption_population(&synchronized);

    let source = ExactSynchronizedOccurrenceFibre::found(
        "sens3/grid/bbaf2n/open-world-tube",
        None,
        GRID,
        whole.body,
        synchronized,
        vec!["later world consequence remains open".to_owned()],
    )
    .map_err(display)?;
    let expected_source = source.clone();
    let source_sha256 = source.source_identity_sha256.clone();
    let incidence_sha256 = source.incidence_identity_sha256.clone();
    let (presented_section, presented_current) =
        physical_current(&audio, &video, precursor_ablated)?;
    let dimension = BaseUnits::declare(["sensory-world-current"])
        .map_err(display)?
        .unit("sensory-world-current")
        .map_err(display)?;
    let chart = ExactMembraneChartPassage::identity(
        dimension,
        presented_section.clone(),
        presented_current.clone(),
    );

    let rest = RecurrentGranularReturnedAffineAthenaRest::read(
        &fs::read(root.join(PREDECESSOR)).map_err(display)?,
    )
    .map_err(display)?;
    let rested_identity = rest.identity().to_owned();
    let mut membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?
        .mount_resident_factor_receiver_faces()
        .map_err(display)?;
    eprintln!("sens3 phase: exact source and resident factor-current front mounted");
    let returned = membrane
        .recur_open_world_tube(source.into_exterior_fibre().map_err(display)?, &[chart])
        .map_err(display)?;
    eprintln!(
        "sens3 phase: orders={} silence={} radiation={}",
        returned.receipt.current_returns[0].orders.len(),
        returned.receipt.lawful_silence_present,
        returned.receipt.compulsory_nonradical_radiation_present,
    );
    let recovered = returned
        .exterior
        .recover::<ExactSynchronizedOccurrenceFibre>()
        .map_err(|_| "the complete synchronized source fibre did not return".to_owned())?;
    let exact_source_recovered = recovered == expected_source;
    let returned_rest = membrane.into_rest();
    let rested_identity_returned_unchanged = returned_rest.identity() == rested_identity;
    let receipt = Sens3Probe {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        precursor_ablated,
        source_sha256,
        incidence_sha256,
        whole_fragment_population: whole.fragment_population,
        rechunked_fragment_population: rechunked.fragment_population,
        packetization_natural_before_native_contact,
        synchronized_contact_population: contacts.len(),
        source_cell_population,
        ignored_source_cell_population,
        overlapping_contact_population,
        interruption_contact_population,
        presented_section,
        presented_current,
        native_return: returned.receipt,
        exact_source_recovered,
        rested_identity_returned_unchanged,
    };
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join(if precursor_ablated {
            "02-precursor-ablated-open-world-tube.json"
        } else {
            "01-primary-open-world-tube.json"
        }),
        serde_json::to_vec_pretty(&receipt).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn grade_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let primary: serde_json::Value = serde_json::from_slice(
        &fs::read(output.join("01-primary-open-world-tube.json")).map_err(display)?,
    )
    .map_err(display)?;
    let ablated: serde_json::Value = serde_json::from_slice(
        &fs::read(output.join("02-precursor-ablated-open-world-tube.json")).map_err(display)?,
    )
    .map_err(display)?;
    let primary_orders = orders(&primary)?;
    let ablated_orders = orders(&ablated)?;
    if primary_orders.len() < 2 || ablated_orders.len() < 2 {
        return Err("SENS3 did not return both immediate and later causal orders".to_owned());
    }
    let primary_first_ports = ports(&primary_orders[0])?;
    let primary_later_ports = ports(&primary_orders[1])?;
    let ablated_later_ports = ports(&ablated_orders[1])?;
    if primary_first_ports.len() != primary_later_ports.len()
        || primary_later_ports.len() != ablated_later_ports.len()
    {
        return Err("the SENS3 control changed the outward port address population".to_owned());
    }
    let persistent_lawful_silence_port_population = primary_first_ports
        .iter()
        .zip(primary_later_ports)
        .filter(|(immediate, later)| radical(immediate) && radical(later))
        .count();
    let precursor_attributable_later_response_population = primary_later_ports
        .iter()
        .zip(ablated_later_ports)
        .filter(|(primary, ablated)| primary["returned_response"] != ablated["returned_response"])
        .count();
    let first_projective = &primary_orders[0]["projective_descent"];
    let source_rays = json_usize(first_projective, "source_ray_population")?;
    let target_rays = json_usize(first_projective, "target_ray_population")?;
    let primary_terminal = &primary["native_return"]["current_returns"][0]["terminal"];
    let ablated_terminal = &ablated["native_return"]["current_returns"][0]["terminal"];
    let native_primary = &primary["native_return"];
    let native_ablated = &ablated["native_return"];
    let returned = Sens3Return {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        primary_return_identity_sha256: json_string(native_primary, "identity_sha256")?,
        ablated_return_identity_sha256: json_string(native_ablated, "identity_sha256")?,
        packetization_naturality_returned: json_bool(
            &primary,
            "packetization_natural_before_native_contact",
        )? && json_bool(
            &ablated,
            "packetization_natural_before_native_contact",
        )?,
        ignored_interval_population: json_usize(&primary, "ignored_source_cell_population")?,
        overlap_interval_population: json_usize(&primary, "overlapping_contact_population")?,
        interruption_interval_population: json_usize(&primary, "interruption_contact_population")?,
        internally_retained_new_ray_population: target_rays.saturating_sub(source_rays),
        immediately_radiated_port_population: json_usize(
            &primary_orders[0],
            "compulsory_radiation_population",
        )?,
        delayed_radiated_port_population: json_usize(
            &primary_orders[1],
            "compulsory_radiation_population",
        )?,
        persistent_lawful_silence_port_population,
        precursor_attributable_later_response_population,
        precursor_ablation_preserved_native_topology: primary_terminal["terminal"]
            == ablated_terminal["terminal"]
            && primary_terminal["projective_ray_population"]
                == ablated_terminal["projective_ray_population"]
            && native_primary["outward_port_population"]
                == native_ablated["outward_port_population"],
        exact_dynamic_condensation_returned: primary_terminal["terminal"]
            == "dynamically-condensed-rest"
            && ablated_terminal["terminal"] == "dynamically-condensed-rest"
            && json_bool(
                native_primary,
                "exact_dynamic_condensation_or_open_front_returned",
            )?
            && json_bool(
                native_ablated,
                "exact_dynamic_condensation_or_open_front_returned",
            )?,
        exact_source_fibres_returned: json_bool(&primary, "exact_source_recovered")?
            && json_bool(&ablated, "exact_source_recovered")?,
        same_rest_returned_unchanged: json_bool(&primary, "rested_identity_returned_unchanged")?
            && json_bool(&ablated, "rested_identity_returned_unchanged")?,
        every_generator_descent_returned_on_card: json_bool(
            native_primary,
            "every_generator_descent_returned_on_card",
        )? && json_bool(
            native_ablated,
            "every_generator_descent_returned_on_card",
        )?,
        word_or_clause_renderer_ran: json_bool(native_primary, "word_or_clause_renderer_ran")?
            || json_bool(native_ablated, "word_or_clause_renderer_ran")?,
        wake_word_or_vad_gate_present: json_bool(native_primary, "wake_word_or_vad_gate_present")?
            || json_bool(native_ablated, "wake_word_or_vad_gate_present")?,
        timer_or_maximum_turn_present: json_bool(native_primary, "timer_or_maximum_turn_present")?
            || json_bool(native_ablated, "timer_or_maximum_turn_present")?,
        host_selected_native_contact: json_bool(native_primary, "host_selected_native_contact")?
            || json_bool(native_ablated, "host_selected_native_contact")?,
        invariant_transport_reuploaded: json_bool(
            native_primary,
            "invariant_transport_reuploaded",
        )? || json_bool(
            native_ablated,
            "invariant_transport_reuploaded",
        )?,
        cpu_semantic_replay_after_device: json_bool(
            native_primary,
            "cpu_semantic_replay_after_device",
        )? || json_bool(
            native_ablated,
            "cpu_semantic_replay_after_device",
        )?,
    };
    if !returned.packetization_naturality_returned
        || returned.ignored_interval_population == 0
        || returned.overlap_interval_population == 0
        || returned.interruption_interval_population == 0
        || returned.internally_retained_new_ray_population == 0
        || returned.immediately_radiated_port_population == 0
        || returned.delayed_radiated_port_population == 0
        || returned.persistent_lawful_silence_port_population == 0
        || returned.precursor_attributable_later_response_population == 0
        || !returned.precursor_ablation_preserved_native_topology
        || !returned.exact_dynamic_condensation_returned
        || !returned.exact_source_fibres_returned
        || !returned.same_rest_returned_unchanged
        || !returned.every_generator_descent_returned_on_card
        || returned.word_or_clause_renderer_ran
        || returned.wake_word_or_vad_gate_present
        || returned.timer_or_maximum_turn_present
        || returned.host_selected_native_contact
        || returned.invariant_transport_reuploaded
        || returned.cpu_semantic_replay_after_device
    {
        return Err("the SENS3 qualitative receiver did not pass".to_owned());
    }
    fs::write(
        output.join("00-sens3-return.json"),
        serde_json::to_vec_pretty(&returned).map_err(display)?,
    )
    .map_err(display)
}

fn orders(value: &serde_json::Value) -> Result<&Vec<serde_json::Value>, String> {
    value["native_return"]["current_returns"][0]["orders"]
        .as_array()
        .ok_or_else(|| "the SENS3 receipt lost its causal orders".to_owned())
}

fn ports(order: &serde_json::Value) -> Result<&Vec<serde_json::Value>, String> {
    order["outward_port_returns"]
        .as_array()
        .ok_or_else(|| "a SENS3 order lost its outward port family".to_owned())
}

fn radical(port: &serde_json::Value) -> bool {
    port["lies_in_outward_radical"].as_bool().unwrap_or(false)
}

fn json_usize(value: &serde_json::Value, field: &str) -> Result<usize, String> {
    value[field]
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| format!("the SENS3 receipt lost integer field {field}"))
}

fn json_bool(value: &serde_json::Value, field: &str) -> Result<bool, String> {
    value[field]
        .as_bool()
        .ok_or_else(|| format!("the SENS3 receipt lost boolean field {field}"))
}

fn json_string(value: &serde_json::Value, field: &str) -> Result<String, String> {
    value[field]
        .as_str()
        .map(ToOwned::to_owned)
        .ok_or_else(|| format!("the SENS3 receipt lost string field {field}"))
}

fn interruption_population(synchronized: &ExactSynchronizedOccurrence) -> usize {
    let left = &synchronized.sections[0];
    let right = &synchronized.sections[1];
    left.cells
        .iter()
        .flat_map(|left_cell| {
            let left_begin = left.clock.transport(&left_cell.local_begin);
            let left_end = left.clock.transport(&left_cell.local_end);
            right.cells.iter().filter(move |right_cell| {
                let right_begin = right.clock.transport(&right_cell.local_begin);
                let right_end = right.clock.transport(&right_cell.local_end);
                (left_begin < right_begin && right_begin < left_end)
                    || (right_begin < left_begin && left_begin < right_end)
            })
        })
        .count()
}

fn assemble(body: &[u8], widths: &[usize]) -> Result<CompleteAddressedMemorySpan, String> {
    let mut span = AddressedMemorySpan::found(
        "sens3/grid/bbaf2n/open-world-tube",
        body.len() as u64,
        sha256(body),
    )
    .map_err(|error| format!("{error:?}"))?;
    let mut from = 0_usize;
    let mut at = 0_usize;
    while from < body.len() {
        let width = widths[at % widths.len()].max(1);
        let to = body.len().min(from.saturating_add(width));
        (span, _) = span
            .admit(MemorySpanFragment::new(
                "sens3/grid/bbaf2n/open-world-tube",
                from as u64,
                body[from..to].to_vec(),
            ))
            .map_err(|failure| format!("{:?}", failure.defect))?;
        from = to;
        at += 1;
    }
    span.close()
        .map_err(|failure| format!("{:?}", failure.defect))
}

fn synchronized_occurrence(
    audio: &[i16],
    video: &[u8],
    ablate_precursor: bool,
) -> Result<ExactSynchronizedOccurrence, String> {
    let audio_clock = ExactClockTransport::new(
        rat(0),
        rat(0),
        Rat::new(BigInt::from(1), BigInt::from(AUDIO_HZ)),
    )
    .map_err(display)?;
    let video_clock = ExactClockTransport::new(
        rat(0),
        rat(0),
        Rat::new(BigInt::from(1), BigInt::from(VIDEO_HZ)),
    )
    .map_err(display)?;
    let audio_start = usize::from(ablate_precursor);
    let mut audio_cells = Vec::new();
    for at in audio_start..AUDIO_CELL_COUNT {
        let begin = at * SAMPLES_PER_FRAME;
        let end = begin + SAMPLES_PER_FRAME;
        let body = bytemuck_i16(&audio[begin..end]);
        audio_cells.push(
            TimedReceiverCell::new(
                SynchronizedCellId(100 + at as u64),
                ReceiverChartIdentity::new(0x4155_4400 + at as u64),
                stable_u64(body),
                relation_atom(material_i64(body)).map_err(display)?,
                rat(begin as i64),
                rat(end as i64),
                0,
                SynchronizedCellOrigin::Inherited,
            )
            .map_err(display)?,
        );
    }
    let video_covers = [(0_usize, 2_usize), (2, 3), (3, 4)];
    let mut video_cells = Vec::new();
    for (at, (begin, end)) in video_covers.into_iter().enumerate() {
        let body = &video[begin * FRAME_PIXELS..end * FRAME_PIXELS];
        video_cells.push(
            TimedReceiverCell::new(
                SynchronizedCellId(200 + at as u64),
                ReceiverChartIdentity::new(0x5649_4400 + at as u64),
                stable_u64(body),
                relation_atom(material_i64(body)).map_err(display)?,
                rat(begin as i64),
                rat(end as i64),
                0,
                SynchronizedCellOrigin::Inherited,
            )
            .map_err(display)?,
        );
    }
    ExactSynchronizedOccurrence::new(
        stable_u64(&video[..VIDEO_FRAME_COUNT * FRAME_PIXELS]),
        ReceiverChartIdentity::new(0x5345_4e53_33),
        relation_atom(material_i64(bytemuck_i16(
            &audio[..AUDIO_CELL_COUNT * SAMPLES_PER_FRAME],
        )))
        .map_err(display)?,
        1,
        vec![
            SynchronizedReceiverSection::new(AUDIO, audio_clock, audio_cells).map_err(display)?,
            SynchronizedReceiverSection::new(VIDEO, video_clock, video_cells).map_err(display)?,
        ],
        [SynchronizedInteraction::new(AUDIO, VIDEO).map_err(display)?],
    )
    .map_err(display)
}

fn physical_current(
    audio: &[i16],
    video: &[u8],
    ablate_precursor: bool,
) -> Result<(ExactComplexWaveCurrent, ExactComplexWaveCurrent), String> {
    let audio_start = usize::from(ablate_precursor) * SAMPLES_PER_FRAME;
    let audio_end = 4 * SAMPLES_PER_FRAME;
    let acoustic_sum = audio[audio_start..audio_end]
        .iter()
        .try_fold(0_i64, |sum, sample| sum.checked_add(i64::from(*sample)))
        .ok_or("acoustic current overflow")?;
    let optical_sum = video[..VIDEO_FRAME_COUNT * FRAME_PIXELS]
        .iter()
        .try_fold(0_i64, |sum, pixel| sum.checked_add(i64::from(*pixel) - 128))
        .ok_or("optical current overflow")?;
    let early = audio[audio_start..audio_start + SAMPLES_PER_FRAME]
        .iter()
        .map(|sample| i64::from(*sample))
        .sum::<i64>();
    let late = audio[audio_end - SAMPLES_PER_FRAME..audio_end]
        .iter()
        .map(|sample| i64::from(*sample))
        .sum::<i64>();
    let section = ExactComplexWaveCurrent::new(rat(late - early), rat(optical_sum));
    let current = ExactComplexWaveCurrent::new(rat(acoustic_sum), rat(optical_sum));
    if current.is_zero() {
        return Err("the real GRID current collapsed exactly to zero".to_owned());
    }
    Ok((section, current))
}

fn decode_audio(path: &Path) -> Result<Vec<i16>, String> {
    let output = Command::new("ffmpeg")
        .args(["-v", "error", "-i"])
        .arg(path)
        .args([
            "-map", "0:a:0", "-t", "0.10", "-ac", "1", "-ar", "8000", "-f", "s16le", "-",
        ])
        .output()
        .map_err(display)?;
    if !output.status.success() || output.stdout.len() % 2 != 0 {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(output
        .stdout
        .chunks_exact(2)
        .map(|pair| i16::from_le_bytes([pair[0], pair[1]]))
        .collect())
}

fn decode_video(path: &Path) -> Result<Vec<u8>, String> {
    let output = Command::new("ffmpeg")
        .args(["-v", "error", "-i"])
        .arg(path)
        .args([
            "-map",
            "0:v:0",
            "-vf",
            "scale=90:72,format=gray",
            "-frames:v",
            "4",
            "-f",
            "rawvideo",
            "-",
        ])
        .output()
        .map_err(display)?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(output.stdout)
}

fn bytemuck_i16(values: &[i16]) -> &[u8] {
    // SAFETY: `i16` has no invalid bit patterns and the returned view cannot outlive the slice.
    unsafe { std::slice::from_raw_parts(values.as_ptr().cast::<u8>(), values.len() * 2) }
}

fn material_i64(bytes: &[u8]) -> i64 {
    let digest = Sha256::digest(bytes);
    let mut word = [0_u8; 8];
    word.copy_from_slice(&digest[..8]);
    let value = u64::from_le_bytes(word) & 0x3fff_ffff_ffff_ffff;
    i64::try_from(value.max(1)).expect("the masked material coordinate fits i64")
}

fn stable_u64(bytes: &[u8]) -> u64 {
    let digest = Sha256::digest(bytes);
    let mut word = [0_u8; 8];
    word.copy_from_slice(&digest[8..16]);
    u64::from_le_bytes(word).max(1)
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

fn workspace_root() -> Result<PathBuf, String> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
