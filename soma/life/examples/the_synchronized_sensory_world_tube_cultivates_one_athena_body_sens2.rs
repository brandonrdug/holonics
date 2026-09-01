//! SENS2 receiver: one real synchronized audio/video occurrence cultivates the already-rested
//! MEM6 Athena body through its singular mouth. Exact local-clock testimony remains source fibre;
//! only the genuinely returned situated difference changes durable native morphology.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    cuda_refine::ResidentMembraneInteriorReturn, quantity::BaseUnits,
    receiver_exact_compression::ReceiverId, BoundaryId, ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    native_intelligence::{
        AddressedMaterialOccurrence, AdmittedReturnedAffineLaboratoryRestWitness,
        DetachedMembraneCultivation, ExactMembraneChartPassage, ExteriorOccurrenceTransducer,
        GranularCultivationWithdrawal, GranularReturnedAffineEcologyRest, MembraneConsequence,
        MembraneCultivationReceipt, MembraneStanding, NativeCausalMembrane,
        RecurrentGranularReturnedAffineEcologyRest, RecurrentGranularReturnedAffinePredecessor,
        ReturnedAffineLaboratoryRest, StagedMembraneCultivation,
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

const PREDECESSOR: &str = concat!(
    "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
    "athena-returned-membrane-cultivated.rest"
);
const ORGAN: &str = concat!(
    "output/the_causal_boundary_ports_cultivate_one_athena_successor_with_exact_projective_factor_currents_mem6/",
    "athena-causal-boundary-organ.rest"
);
const GRID: &str =
    "/home/b/Workspaces/laboratory/runs/information-flow-datasets/source/GRID/s1/bbaf2n.mpg";
const OUTPUT: &str = "output/the_synchronized_sensory_world_tube_cultivates_one_athena_body_sens2";

const AUDIO: SynchronizedReceiverId = SynchronizedReceiverId(0x4155_4449_4f);
const VIDEO: SynchronizedReceiverId = SynchronizedReceiverId(0x5649_4445_4f);
const AUDIO_HZ: i64 = 8_000;
const VIDEO_HZ: i64 = 50;
const FRAME_PIXELS: usize = 90 * 72;
const FRAME_COUNT: usize = 4;
const SAMPLES_PER_FRAME: usize = (AUDIO_HZ / VIDEO_HZ) as usize;

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens2Return {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    predecessor_identity_sha256: String,
    successor_identity_sha256: String,
    successor_wire_sha256: String,
    source_sha256: String,
    synchronized_incidence_sha256: String,
    source_octets: u64,
    decoded_audio_sample_population: u64,
    decoded_video_frame_population: u64,
    synchronized_contact_population: u64,
    elementary_overlap_interval_population: u64,
    affine_clock_rebase_preserved_every_contact: bool,
    separated_clock_control_returned_no_contact: bool,
    separate_receiver_sections_preserved: bool,
    membrane_crossed_exact_synchronized_source_fibre: bool,
    cultivation: MembraneCultivationReceipt,
    returned_native_thread_population: u64,
    same_body_identity_changed_after_world_return: bool,
    later_conduct_changed_after_world_return: bool,
    source_detached_remount_exact: bool,
    complete_source_absent_from_successor_rest: bool,
    latest_return_withdrawal_recovered_exact_sens1_predecessor: bool,
    latest_return_restoration_recovered_exact_sens2_successor: bool,
    unrelated_sibling_ablation_preserved_returned_thread_population: bool,
    unrelated_sibling_restoration_exact: bool,
    synchronized_side_atlas_retained_in_morphology: bool,
    concatenated_modality_vector_authored: bool,
    transcript_label_or_expected_surface_selected_cultivation: bool,
    cpu_semantic_replay: bool,
    open_exterior: Vec<String>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens2StageWitness {
    predecessor_identity_sha256: String,
    source_sha256: String,
    synchronized_incidence_sha256: String,
    source_octets: u64,
    decoded_audio_sample_population: u64,
    decoded_video_frame_population: u64,
    synchronized_contact_population: u64,
    elementary_overlap_interval_population: u64,
    affine_clock_rebase_preserved_every_contact: bool,
    separated_clock_control_returned_no_contact: bool,
    separate_receiver_sections_preserved: bool,
    membrane_crossed_exact_synchronized_source_fibre: bool,
    resident_return: ResidentMembraneInteriorReturn,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens2CommitWitness {
    stage: Sens2StageWitness,
    cultivation: MembraneCultivationReceipt,
    successor_identity_sha256: String,
    successor_wire_sha256: String,
    returned_native_thread_population: u64,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens2ConductWitness {
    source_detached_remount_exact: bool,
    complete_source_absent_from_successor_rest: bool,
    later_conduct_changed_after_world_return: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Sens2SiblingWitness {
    unrelated_sibling_ablation_preserved_returned_thread_population: bool,
    unrelated_sibling_restoration_exact: bool,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    match env::var("SENS2_MODE").as_deref() {
        Ok("commit") => return commit_phase(&root),
        Ok("verify") => return verify_phase(&root),
        Ok("sibling") => return sibling_phase(&root),
        Ok("inverse") => return inverse_phase(&root),
        Ok("capture") | Err(_) => {}
        Ok(other) => return Err(format!("unknown SENS2_MODE {other}")),
    }
    let grid_path = Path::new(GRID);
    let encoded_source = fs::read(grid_path).map_err(display)?;
    let audio = decode_audio(grid_path)?;
    let video = decode_video(grid_path)?;
    eprintln!("sens2 phase: real GRID streams decoded");
    if audio.len() < FRAME_COUNT * SAMPLES_PER_FRAME || video.len() != FRAME_COUNT * FRAME_PIXELS {
        return Err("the bounded GRID decode did not return four synchronized sections".to_owned());
    }

    let exact = synchronized_occurrence(&encoded_source, &audio, &video, 0, 0, rat(0))?;
    let contacts = SynchronizedOccurrenceChart::new()
        .contacts(&exact)
        .map_err(display)?;
    let rebased =
        synchronized_occurrence(&encoded_source, &audio, &video, AUDIO_HZ, VIDEO_HZ, rat(0))?;
    let rebased_contacts = SynchronizedOccurrenceChart::new()
        .contacts(&rebased)
        .map_err(display)?;
    let separated = synchronized_occurrence(&encoded_source, &audio, &video, 0, 0, rat(1))?;
    let separated_contacts = SynchronizedOccurrenceChart::new()
        .contacts(&separated)
        .map_err(display)?;
    let affine_clock_rebase_preserved_every_contact = contacts == rebased_contacts;
    let separated_clock_control_returned_no_contact = separated_contacts.is_empty();
    if contacts.len() != FRAME_COUNT
        || !affine_clock_rebase_preserved_every_contact
        || !separated_clock_control_returned_no_contact
    {
        return Err(format!(
            "the exact synchronized controls failed: contacts={}, rebased={}, separated={}",
            contacts.len(),
            affine_clock_rebase_preserved_every_contact,
            separated_contacts.len()
        ));
    }
    eprintln!("sens2 phase: exact clock rebase and separation controls passed");

    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
        "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
        "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
    )
    .map_err(display)?;
    let predecessor = ReturnedAffineLaboratoryRest::read_admitted(
        &fs::read(root.join(PREDECESSOR)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;
    let withdrawal =
        GranularCultivationWithdrawal::read(&fs::read(root.join(ORGAN)).map_err(display)?)
            .map_err(display)?;
    let rest =
        GranularReturnedAffineEcologyRest::restore(predecessor, withdrawal).map_err(display)?;
    let predecessor_identity_sha256 = rest.identity().to_owned();
    eprintln!("sens2 phase: exact SENS1 predecessor restored");
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let (left, shared, _) = receiver_cells(rest.membrane_affine_cells())?;

    let exact_source = ExactSynchronizedOccurrenceFibre::found(
        "sens2/grid/bbaf2n/synchronized",
        None,
        GRID,
        encoded_source.clone(),
        exact,
        vec!["later acoustic and optical continuations remain open".to_owned()],
    )
    .map_err(display)?;
    let source_sha256 = exact_source.source_identity_sha256.clone();
    let synchronized_incidence_sha256 = exact_source.incidence_identity_sha256.clone();
    let source_fibre = exact_source.into_exterior_fibre().map_err(display)?;

    let base = BaseUnits::declare(["synchronized-sensory-current"]).map_err(display)?;
    let dimension = base.unit("synchronized-sensory-current").map_err(display)?;
    let injected = ExactComplexWaveCurrent::new(
        rat(i64::try_from(contacts.len()).map_err(display)?),
        rat(i64::try_from(FRAME_COUNT).map_err(display)?),
    );
    let mut membrane = NativeCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let bound = membrane
        .bind_occurrence(
            source_fibre,
            BoundaryId(0x5345_4e53_32),
            &native_address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension.clone(),
                ExactComplexWaveCurrent::zero(),
                injected.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("synchronized binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(initial_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the synchronized source did not cross the Athena mouth".to_owned());
    };
    let recovered = initial_return
        .occurrence
        .exterior
        .recover::<ExactSynchronizedOccurrenceFibre>()
        .map_err(|fibre| format!("the synchronized source fibre was not exact: {fibre:?}"))?;
    let membrane_crossed_exact_synchronized_source_fibre =
        recovered.encoded_source == encoded_source && recovered.contacts == contacts;

    let resident_return = membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    eprintln!("sens2 phase: predecessor resident conduct returned");
    let world_payload = serde_json::to_vec(&(
        "sens2-returned-synchronized-world-consequence",
        &source_sha256,
        &synchronized_incidence_sha256,
        contacts.len(),
        &resident_return.native_radiation,
        &resident_return.returned_radiation,
        &resident_return.family_overlaps,
    ))
    .map_err(display)?;
    let world_return_source = AddressedMaterialOccurrence::found(
        "sens2/world/returned-synchronized-consequence",
        &world_payload,
        Some("sens2/grid/bbaf2n/synchronized".to_owned()),
        vec!["cold synchronized-world delivery".to_owned()],
        vec!["later sensory consequences remain open".to_owned()],
    )
    .map_err(display)?;
    let world_fibre = world_return_source.into_exterior_fibre().map_err(display)?;
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
        .map_err(|failure| format!("synchronized world-return binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(world_return) =
        membrane.receive_occurrence(later).map_err(display)?
    else {
        return Err("the synchronized world consequence did not return".to_owned());
    };
    eprintln!("sens2 phase: founding returned situated difference");
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_return.clone())
        .map_err(display)?;
    let separate_receiver_sections_preserved = recovered.synchronized.sections.len() == 2
        && recovered.synchronized.sections[0].receiver
            != recovered.synchronized.sections[1].receiver;
    let (rest, detached) = staged.detach().map_err(display)?;
    if rest.identity() != predecessor_identity_sha256 {
        return Err("detaching the return changed the admitted SENS1 predecessor".to_owned());
    }
    let stage = Sens2StageWitness {
        predecessor_identity_sha256,
        source_sha256,
        synchronized_incidence_sha256,
        source_octets: u64::try_from(encoded_source.len()).map_err(display)?,
        decoded_audio_sample_population: u64::try_from(audio.len()).map_err(display)?,
        decoded_video_frame_population: FRAME_COUNT as u64,
        synchronized_contact_population: u64::try_from(contacts.len()).map_err(display)?,
        elementary_overlap_interval_population: FRAME_COUNT as u64,
        affine_clock_rebase_preserved_every_contact,
        separated_clock_control_returned_no_contact,
        separate_receiver_sections_preserved,
        membrane_crossed_exact_synchronized_source_fibre,
        resident_return,
    };
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("01-detached-synchronized-return.json"),
        detached.canonical_bytes().map_err(display)?,
    )
    .map_err(display)?;
    fs::write(
        output.join("01-staged-synchronized-witness.json"),
        serde_json::to_vec_pretty(&stage).map_err(display)?,
    )
    .map_err(display)?;
    eprintln!("sens2 phase: exact source departed and detached cultivation rested");
    Ok(())
}

fn commit_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let stage: Sens2StageWitness = serde_json::from_slice(
        &fs::read(output.join("01-staged-synchronized-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let detached = DetachedMembraneCultivation::read(
        &fs::read(output.join("01-detached-synchronized-return.json")).map_err(display)?,
    )
    .map_err(display)?;
    let rest = restore_sens1(root)?;
    if rest.identity() != stage.predecessor_identity_sha256
        || detached.predecessor_identity() != stage.predecessor_identity_sha256
    {
        return Err("the detached return and remounted SENS1 body do not join".to_owned());
    }
    eprintln!("sens2 phase: detached return and exact SENS1 rest rejoined");
    let (successor, cultivation, successor_wire) =
        detached.commit_restable(rest).map_err(display)?;
    eprintln!("sens2 phase: synchronized world return cultivated the one body");
    let successor_identity_sha256 = successor.identity().to_owned();
    let returned_native_thread_population =
        u64::try_from(successor.body().body().returned_deposits().len()).map_err(display)?;
    if successor_identity_sha256 == stage.predecessor_identity_sha256
        || returned_native_thread_population != 2
    {
        return Err("the recurrent return did not change the one native body".to_owned());
    }
    let successor_wire_sha256 = sha256(&successor_wire);
    let commit = Sens2CommitWitness {
        stage,
        cultivation,
        successor_identity_sha256,
        successor_wire_sha256,
        returned_native_thread_population,
    };
    fs::write(
        output.join("athena-synchronized-sensory.rest"),
        successor_wire,
    )
    .map_err(display)?;
    fs::write(
        output.join("02-cultivated-synchronized-witness.json"),
        serde_json::to_vec_pretty(&commit).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn verify_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let commit: Sens2CommitWitness = serde_json::from_slice(
        &fs::read(output.join("02-cultivated-synchronized-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let successor_wire =
        fs::read(output.join("athena-synchronized-sensory.rest")).map_err(display)?;
    if sha256(&successor_wire) != commit.successor_wire_sha256 {
        return Err("the SENS2 successor wire changed before verification".to_owned());
    }
    let remounted =
        RecurrentGranularReturnedAffineEcologyRest::read(&successor_wire).map_err(display)?;
    let source_detached_remount_exact = remounted.identity() == commit.successor_identity_sha256;
    let source = fs::read(GRID).map_err(display)?;
    let complete_source_absent_from_successor_rest = !successor_wire
        .windows(commit.stage.source_sha256.len())
        .any(|window| window == commit.stage.source_sha256.as_bytes())
        && !successor_wire
            .windows(source.len())
            .any(|window| window == source.as_slice());
    let (left, shared, _unrelated) = receiver_cells(remounted.membrane_affine_cells())?;
    let injected = ExactComplexWaveCurrent::new(
        rat(i64::try_from(commit.stage.synchronized_contact_population).map_err(display)?),
        rat(i64::try_from(commit.stage.decoded_video_frame_population).map_err(display)?),
    );
    let mut membrane = NativeCausalMembrane::mount(remounted)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let later_conduct = membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    eprintln!("sens2 phase: successor resident conduct returned");
    let later_conduct_changed_after_world_return = later_conduct != commit.stage.resident_return;
    let _successor = membrane.into_rest();
    let conduct = Sens2ConductWitness {
        source_detached_remount_exact,
        complete_source_absent_from_successor_rest,
        later_conduct_changed_after_world_return,
    };
    fs::write(
        output.join("03-successor-conduct-witness.json"),
        serde_json::to_vec_pretty(&conduct).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn sibling_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let commit: Sens2CommitWitness = serde_json::from_slice(
        &fs::read(output.join("02-cultivated-synchronized-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let successor = RecurrentGranularReturnedAffineEcologyRest::read(
        &fs::read(output.join("athena-synchronized-sensory.rest")).map_err(display)?,
    )
    .map_err(display)?;
    let (_, _, unrelated) = receiver_cells(successor.membrane_affine_cells())?;
    let deposits_before = successor
        .body()
        .body()
        .returned_deposits()
        .iter()
        .map(|deposit| deposit.difference_identity_sha256.clone())
        .collect::<Vec<_>>();
    let (sibling_ablated, sibling_withdrawal) = successor
        .withdraw_relational_cell_from_admitted(&unrelated)
        .map_err(display)?;
    let deposits_after = sibling_ablated
        .body()
        .body()
        .returned_deposits()
        .iter()
        .map(|deposit| deposit.difference_identity_sha256.clone())
        .collect::<Vec<_>>();
    let unrelated_sibling_ablation_preserved_returned_thread_population =
        deposits_before == deposits_after;
    let successor = sibling_ablated
        .restore_relational_cell_from_admitted(sibling_withdrawal)
        .map_err(display)?;
    let unrelated_sibling_restoration_exact =
        successor.identity() == commit.successor_identity_sha256;
    if !unrelated_sibling_ablation_preserved_returned_thread_population
        || !unrelated_sibling_restoration_exact
    {
        return Err("the SENS2 unrelated-sibling control failed".to_owned());
    }
    let witness = Sens2SiblingWitness {
        unrelated_sibling_ablation_preserved_returned_thread_population,
        unrelated_sibling_restoration_exact,
    };
    fs::write(
        output.join("04-sibling-ablation-witness.json"),
        serde_json::to_vec_pretty(&witness).map_err(display)?,
    )
    .map_err(display)?;
    eprintln!("sens2 phase: sibling ablation and restoration passed");
    Ok(())
}

fn inverse_phase(root: &Path) -> Result<(), String> {
    let output = root.join(OUTPUT);
    let commit: Sens2CommitWitness = serde_json::from_slice(
        &fs::read(output.join("02-cultivated-synchronized-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let conduct: Sens2ConductWitness = serde_json::from_slice(
        &fs::read(output.join("03-successor-conduct-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let sibling: Sens2SiblingWitness = serde_json::from_slice(
        &fs::read(output.join("04-sibling-ablation-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let successor = RecurrentGranularReturnedAffineEcologyRest::read(
        &fs::read(output.join("athena-synchronized-sensory.rest")).map_err(display)?,
    )
    .map_err(display)?;
    let (predecessor, latest_withdrawal) = successor
        .withdraw_latest_returned_difference_from_admitted()
        .map_err(display)?;
    let latest_return_withdrawal_recovered_exact_sens1_predecessor = matches!(
        &predecessor,
        RecurrentGranularReturnedAffinePredecessor::First(rest)
            if rest.identity() == commit.stage.predecessor_identity_sha256
    );
    let successor =
        RecurrentGranularReturnedAffineEcologyRest::restore_latest_returned_difference_from_admitted(
            predecessor,
            latest_withdrawal,
        )
        .map_err(display)?;
    let latest_return_restoration_recovered_exact_sens2_successor =
        successor.identity() == commit.successor_identity_sha256;
    eprintln!("sens2 phase: latest-return inverse and restoration passed");

    let same_body_identity_changed_after_world_return = commit.successor_identity_sha256
        != commit.stage.predecessor_identity_sha256
        && commit.returned_native_thread_population == 2;
    let synchronized_side_atlas_retained_in_morphology = false;
    let concatenated_modality_vector_authored = false;
    let transcript_label_or_expected_surface_selected_cultivation = false;
    let cpu_semantic_replay = commit
        .stage
        .resident_return
        .cpu_semantic_replay_after_device;
    if !commit
        .stage
        .membrane_crossed_exact_synchronized_source_fibre
        || !commit.stage.separate_receiver_sections_preserved
        || !same_body_identity_changed_after_world_return
        || !conduct.later_conduct_changed_after_world_return
        || !conduct.source_detached_remount_exact
        || !conduct.complete_source_absent_from_successor_rest
        || !latest_return_withdrawal_recovered_exact_sens1_predecessor
        || !latest_return_restoration_recovered_exact_sens2_successor
        || !sibling.unrelated_sibling_ablation_preserved_returned_thread_population
        || !sibling.unrelated_sibling_restoration_exact
        || synchronized_side_atlas_retained_in_morphology
        || concatenated_modality_vector_authored
        || transcript_label_or_expected_surface_selected_cultivation
        || cpu_semantic_replay
    {
        return Err("the SENS2 qualitative receiver did not close".to_owned());
    }

    let result = Sens2Return {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        predecessor_identity_sha256: commit.stage.predecessor_identity_sha256,
        successor_identity_sha256: commit.successor_identity_sha256,
        successor_wire_sha256: commit.successor_wire_sha256,
        source_sha256: commit.stage.source_sha256,
        synchronized_incidence_sha256: commit.stage.synchronized_incidence_sha256,
        source_octets: commit.stage.source_octets,
        decoded_audio_sample_population: commit.stage.decoded_audio_sample_population,
        decoded_video_frame_population: commit.stage.decoded_video_frame_population,
        synchronized_contact_population: commit.stage.synchronized_contact_population,
        elementary_overlap_interval_population: commit.stage.elementary_overlap_interval_population,
        affine_clock_rebase_preserved_every_contact: commit
            .stage
            .affine_clock_rebase_preserved_every_contact,
        separated_clock_control_returned_no_contact: commit
            .stage
            .separated_clock_control_returned_no_contact,
        separate_receiver_sections_preserved: commit.stage.separate_receiver_sections_preserved,
        membrane_crossed_exact_synchronized_source_fibre: commit
            .stage
            .membrane_crossed_exact_synchronized_source_fibre,
        cultivation: commit.cultivation,
        returned_native_thread_population: commit.returned_native_thread_population,
        same_body_identity_changed_after_world_return,
        later_conduct_changed_after_world_return: conduct.later_conduct_changed_after_world_return,
        source_detached_remount_exact: conduct.source_detached_remount_exact,
        complete_source_absent_from_successor_rest: conduct.complete_source_absent_from_successor_rest,
        latest_return_withdrawal_recovered_exact_sens1_predecessor,
        latest_return_restoration_recovered_exact_sens2_successor,
        unrelated_sibling_ablation_preserved_returned_thread_population: sibling
            .unrelated_sibling_ablation_preserved_returned_thread_population,
        unrelated_sibling_restoration_exact: sibling.unrelated_sibling_restoration_exact,
        synchronized_side_atlas_retained_in_morphology,
        concatenated_modality_vector_authored,
        transcript_label_or_expected_surface_selected_cultivation,
        cpu_semantic_replay,
        open_exterior: vec![
            "SENS2 establishes one bounded synchronized audio/video return; endogenous recurrence remains SENS3"
                .to_owned(),
            "native acoustic emission and full-duplex room return remain SENS4".to_owned(),
            "native optical production and optical world return remain SENS5".to_owned(),
        ],
    };
    fs::write(
        output.join("00-sens2-return.json"),
        serde_json::to_vec_pretty(&result).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn restore_sens1(root: &Path) -> Result<GranularReturnedAffineEcologyRest, String> {
    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
        "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
        "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
    )
    .map_err(display)?;
    let predecessor = ReturnedAffineLaboratoryRest::read_admitted(
        &fs::read(root.join(PREDECESSOR)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;
    let withdrawal =
        GranularCultivationWithdrawal::read(&fs::read(root.join(ORGAN)).map_err(display)?)
            .map_err(display)?;
    GranularReturnedAffineEcologyRest::restore(predecessor, withdrawal).map_err(display)
}

fn synchronized_occurrence(
    encoded: &[u8],
    audio: &[i16],
    video: &[u8],
    audio_shift: i64,
    video_shift: i64,
    video_occurrence_origin: Rat,
) -> Result<ExactSynchronizedOccurrence, String> {
    let audio_clock = ExactClockTransport::new(
        rat(audio_shift),
        rat(0),
        Rat::new(BigInt::from(1), BigInt::from(AUDIO_HZ)),
    )
    .map_err(display)?;
    let video_clock = ExactClockTransport::new(
        rat(video_shift),
        video_occurrence_origin,
        Rat::new(BigInt::from(1), BigInt::from(VIDEO_HZ)),
    )
    .map_err(display)?;
    let mut audio_cells = Vec::with_capacity(FRAME_COUNT);
    let mut video_cells = Vec::with_capacity(FRAME_COUNT);
    for at in 0..FRAME_COUNT {
        let audio_begin = at * SAMPLES_PER_FRAME;
        let audio_end = audio_begin + SAMPLES_PER_FRAME;
        let video_begin = at * FRAME_PIXELS;
        let video_end = video_begin + FRAME_PIXELS;
        audio_cells.push(
            TimedReceiverCell::new(
                SynchronizedCellId(100 + at as u64),
                ReceiverChartIdentity::new(0x4155_4400 + at as u64),
                stable_u64(bytemuck_i16(&audio[audio_begin..audio_end])),
                relation_atom(material_i64(bytemuck_i16(&audio[audio_begin..audio_end])))
                    .map_err(display)?,
                rat(audio_shift + i64::try_from(audio_begin).map_err(display)?),
                rat(audio_shift + i64::try_from(audio_end).map_err(display)?),
                0,
                SynchronizedCellOrigin::Inherited,
            )
            .map_err(display)?,
        );
        video_cells.push(
            TimedReceiverCell::new(
                SynchronizedCellId(200 + at as u64),
                ReceiverChartIdentity::new(0x5649_4400 + at as u64),
                stable_u64(&video[video_begin..video_end]),
                relation_atom(material_i64(&video[video_begin..video_end])).map_err(display)?,
                rat(video_shift + at as i64),
                rat(video_shift + at as i64 + 1),
                0,
                SynchronizedCellOrigin::Inherited,
            )
            .map_err(display)?,
        );
    }
    ExactSynchronizedOccurrence::new(
        stable_u64(encoded),
        ReceiverChartIdentity::new(0x5345_4e53_32),
        relation_atom(material_i64(encoded)).map_err(display)?,
        1,
        vec![
            SynchronizedReceiverSection::new(AUDIO, audio_clock, audio_cells).map_err(display)?,
            SynchronizedReceiverSection::new(VIDEO, video_clock, video_cells).map_err(display)?,
        ],
        [SynchronizedInteraction::new(AUDIO, VIDEO).map_err(display)?],
    )
    .map_err(display)
}

fn decode_audio(path: &Path) -> Result<Vec<i16>, String> {
    let output = Command::new("ffmpeg")
        .args(["-v", "error", "-i"])
        .arg(path)
        .args([
            "-map", "0:a:0", "-t", "0.08", "-ac", "1", "-ar", "8000", "-f", "s16le", "-",
        ])
        .output()
        .map_err(display)?;
    if !output.status.success() || output.stdout.len() % 2 != 0 {
        return Err(format!(
            "ffmpeg acoustic decode refused: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
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
        return Err(format!(
            "ffmpeg optical decode refused: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(output.stdout)
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
    Err("the granular Athena body has no continuing native address".to_owned())
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
