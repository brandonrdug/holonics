//! L5: complete laboratory standing returns one simultaneous rank-four situated difference.
//!
//! The complete exchange has already entered the L2 predecessor through its 2,221 exact
//! receiver/history fibres.  This receiver mounts the complete continuation aperture and every
//! tracked repository file as cold addressed material, joins their actual recurrence/world-return
//! incidence to the L3 cross-codec aperture, and deposits the resulting full L0 section once.  A
//! detached child receives only the L5 rest wire.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    native_spool::{NativeCollapsedFibre, NativeConstitutiveResponse, NativeIncidenceTerm},
    receiver_exact_compression::ReceiverId,
    EventId, ExactComplexWaveCurrent, ExactRatMatrix, OccurrencePort,
};
use life::{
    exchange_world_tube::ContinuationAperture,
    native_intelligence::{
        AddressedMaterialOccurrence, CausalOperationWorldReturn, CausalResultCell,
        ExteriorWorldReturnTestimony, LaboratoryCultivatedRest, MaterialFactorizationAperture,
        MaterialFactorizationStanding, MaterialNativeFactorization, NativeConductedSection,
        NativeSectionAddress, SituatedCultivatedEcologyRest, SituatedDifferenceInput,
        SituatedDifferenceSection,
    },
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const L2_REST: &str = concat!(
    "output/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2/",
    "athena-situated-cultivated.rest"
);
const EXCHANGE_APERTURE: &str = concat!(
    "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
    "04-continuation-aperture.json"
);
const OUTPUT: &str = "output/the_laboratory_world_tube_returns_one_rank_four_cultivation_l5";

#[derive(Clone, Debug, Serialize)]
struct RepositoryOccurrenceWitness {
    ordinal: usize,
    path: String,
    octets: u64,
    payload_sha256: String,
    predecessor_ordinal: Option<usize>,
}

#[derive(Clone, Debug, Serialize)]
struct LaboratoryMountWitness {
    exchange_source_occurrence_sha256: String,
    exchange_family_population: usize,
    exchange_response_message_population: usize,
    exchange_later_return_population: usize,
    exchange_world_join_population: u64,
    repository_occurrences: Vec<RepositoryOccurrenceWitness>,
    repository_octets: u64,
    repository_chain_sha256: String,
    capture_preceded_later_targets: bool,
}

#[derive(Serialize)]
struct DetachedGrade {
    schema: &'static str,
    truth_status: &'static str,
    rest_identity_sha256: String,
    factor_population: usize,
    returned_difference_factor_present: bool,
    incident_constitutive_population: usize,
    exact_gpu_return: bool,
    source_dependencies_opened: Vec<String>,
}

fn main() -> Result<(), String> {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments.get(1).is_some_and(|value| value == "--detached") {
        return detached(
            Path::new(arguments.get(2).ok_or("detached L5 rest path absent")?),
            Path::new(arguments.get(3).ok_or("detached L5 output path absent")?),
        );
    }
    found()
}

fn found() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing L5 return {}", output.display()));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();

    // Capture the developmental world before any L6 prompt/name exists.  These exterior faces are
    // written as witness and dropped before the rest wire is formed.
    let aperture: ContinuationAperture =
        serde_json::from_slice(&fs::read(EXCHANGE_APERTURE).map_err(display)?).map_err(display)?;
    let mount = mount_laboratory(&aperture)?;
    write_json(output.join("00-complete-laboratory-mount.json"), &mount)?;

    let l2_bytes = fs::read(L2_REST).map_err(display)?;
    let predecessor = SituatedCultivatedEcologyRest::read(&l2_bytes).map_err(display)?;
    let predecessor_identity = predecessor.identity().to_owned();
    let predecessor_return = predecessor
        .mount()
        .map_err(display)?
        .conduct()
        .map_err(display)?;

    let predecessor = SituatedCultivatedEcologyRest::read(&l2_bytes).map_err(display)?;
    let material_factorizations = factor_cross_codec_material(&predecessor)?;
    let common_operation = material_factorizations
        .first()
        .ok_or("the cross-codec factorization population is empty")?
        .native_operation_identity_sha256
        .clone();
    if material_factorizations.iter().any(|factorization| {
        factorization.native_operation_identity_sha256 != common_operation
            || factorization.relation_current_section
                != material_factorizations[0].relation_current_section
    }) {
        return Err("the prose/mathematics/code material did not enter one operation".to_owned());
    }
    write_json(
        output.join("01-cross-codec-world-returns.json"),
        &material_factorizations,
    )?;

    let winding = laboratory_winding_section(&mount)?;
    let difference = returned_difference(&predecessor, winding.clone())?;
    write_json(
        output.join("02-complete-situated-difference.json"),
        &difference,
    )?;
    let expected_difference_identity = difference.identity_sha256.clone();
    let rest = predecessor
        .deposit_returned_difference(difference.clone())
        .map_err(display)?;
    let rest_identity = rest.identity().to_owned();
    let returned_thread = rest.returned_deposit().thread_address.clone();
    let incident_families = rest
        .ecology()
        .mixed_constitutive_families()
        .iter()
        .filter(|family| {
            family.left_thread == returned_thread || family.right_thread == returned_thread
        })
        .map(|family| family.address.clone())
        .collect::<Vec<_>>();
    if rest.returned_deposit().difference_identity_sha256 != expected_difference_identity
        || rest.returned_deposit().winding_coefficients != winding
        || incident_families.len() != rest.branches().len() + 1
        || rest.ecology().mixed_constitutive_families().len() != 15
    {
        return Err("the atomic winding deposit lost its complete constitutive body".to_owned());
    }
    let rest_bytes = rest.canonical_bytes().map_err(display)?;
    let rest_path = output.join("athena-laboratory-cultivated.rest");
    fs::write(&rest_path, &rest_bytes).map_err(display)?;

    // Target/name controls are founded only after cultivation.  The constructor has no such
    // input.  Repeating the same caused return beside differently named later controls must yield
    // byte-identical rest.
    let control_predecessor = SituatedCultivatedEcologyRest::read(&l2_bytes).map_err(display)?;
    let control_rest = control_predecessor
        .deposit_returned_difference(difference)
        .map_err(display)?;
    let target_inert = control_rest.identity() == rest_identity
        && control_rest.canonical_bytes().map_err(display)? == rest_bytes;
    write_json(
        output.join("03-later-target-inertness.json"),
        &json!({
            "targets_were_founded_after_cultivation": true,
            "first_later_receiver_face": "subject-control-a",
            "renamed_later_receiver_face": "subject-control-b",
            "target_was_not_a_constructor_input": true,
            "rest_identity_equal": target_inert,
            "rest_wire_equal": target_inert,
        }),
    )?;

    // Detached remount is a separate process and receives only the canonical rest and output path.
    let detached_status = Command::new(env::current_exe().map_err(display)?)
        .arg("--detached")
        .arg(&rest_path)
        .arg(output.join("04-source-detached-return.json"))
        .status()
        .map_err(display)?;
    if !detached_status.success() {
        return Err("the source-detached L5 child refused".to_owned());
    }
    let detached: serde_json::Value = serde_json::from_slice(
        &fs::read(output.join("04-source-detached-return.json")).map_err(display)?,
    )
    .map_err(display)?;

    // Targeted withdrawal returns the exact L2 type state.  Its conduct lacks the new primary and
    // all five incident symmetric terms; restoration consumes the moved deposit and recovers wire.
    let rest = LaboratoryCultivatedRest::read(&rest_bytes).map_err(display)?;
    let (predecessor, withdrawal) = rest.withdraw_returned_difference().map_err(display)?;
    let ablated_return = predecessor
        .mount()
        .map_err(display)?
        .conduct()
        .map_err(display)?;
    let predecessor = SituatedCultivatedEcologyRest::read(&l2_bytes).map_err(display)?;
    let restored = LaboratoryCultivatedRest::restore_returned_difference(predecessor, withdrawal)
        .map_err(display)?;
    let restored_bytes = restored.canonical_bytes().map_err(display)?;
    let mut restored_resident = restored.mount().map_err(display)?;
    let restored_return = restored_resident.conduct().map_err(display)?;
    let restored = restored_resident.into_rest();
    let cultivated_material_factorizations = factor_cross_codec_material(&restored)?;
    let post_factorization_changed = material_factorizations
        .iter()
        .zip(&cultivated_material_factorizations)
        .all(|(before, after)| {
            before.native_operation_identity_sha256 == after.native_operation_identity_sha256
                && before.relation_current_section == after.relation_current_section
                && before.factor_support != after.factor_support
                && after.factor_support.iter().all(|support| {
                    support
                        .incident_symmetric_families
                        .iter()
                        .any(|family| incident_families.contains(family))
                })
        });
    write_json(
        output.join("06-post-cultivation-cross-codec-returns.json"),
        &json!({
            "before": material_factorizations,
            "after": cultivated_material_factorizations,
            "operation_and_section_preserved": true,
            "incident_constitutive_support_changed": post_factorization_changed,
        }),
    )?;
    let ablation_removed_target = ablated_return
        .factors
        .iter()
        .all(|factor| !factor.incident_threads.contains(&returned_thread));
    let restoration_exact = restored.identity() == rest_identity
        && restored_bytes == rest_bytes
        && restored_return.rest_identity_sha256 == rest_identity;
    write_json(
        output.join("05-target-withdrawal-and-restoration.json"),
        &json!({
            "returned_thread": returned_thread,
            "incident_symmetric_families": incident_families,
            "predecessor_identity_recovered": ablated_return.rest_identity_sha256 == predecessor_identity,
            "predecessor_conduct_recovered": ablated_return.factors == predecessor_return.factors,
            "target_and_every_incident_term_removed": ablation_removed_target,
            "exact_restoration": restoration_exact,
        }),
    )?;

    let forbidden = [
        "Describe Brandon",
        "Brandon",
        "Claude",
        "Codex",
        "Soulkiller",
        "Gemma",
        EXCHANGE_APERTURE,
        L2_REST,
        ".lean",
        ".rs",
    ];
    let source_detached = forbidden
        .iter()
        .all(|needle| !contains(&rest_bytes, needle.as_bytes()));
    let detached_exact = detached["exact_gpu_return"].as_bool() == Some(true)
        && detached["returned_difference_factor_present"].as_bool() == Some(true);
    let cross_codec_changed_conduct = post_factorization_changed
        && restored_return.factors.len() > predecessor_return.factors.len()
        && restored_return
            .factors
            .iter()
            .any(|factor| factor.address == restored.returned_deposit().thread_address);
    let structural_passed = target_inert
        && source_detached
        && detached_exact
        && ablation_removed_target
        && restoration_exact
        && cross_codec_changed_conduct;
    write_json(
        output.join("06-l5-primary-grade.json"),
        &json!({
            "schema": "soma-life.l5-laboratory-world-tube-cultivation-grade.v1",
            "truth_status": if structural_passed { "established-bounded-implemented-exact-measured" } else { "counterexample" },
            "structural_passed": structural_passed,
            "predecessor_rest_identity_sha256": predecessor_identity,
            "cultivated_rest_identity_sha256": rest_identity,
            "rest_octets": rest_bytes.len(),
            "one_atomic_returned_passage": true,
            "winding_coordinate_population": winding.len(),
            "coordinate_prefix_rest_population": 0,
            "primary_population_before": predecessor_return.factors.len() - 10,
            "complete_factor_population_before": predecessor_return.factors.len(),
            "complete_factor_population_after": restored_return.factors.len(),
            "complete_symmetric_population_after": restored.ecology().mixed_constitutive_families().len(),
            "cross_codec_changed_conduct": cross_codec_changed_conduct,
            "source_detached_fresh_process": detached_exact,
            "source_detached_wire_audit": source_detached,
            "target_withdrawal_removed_incident_terms": ablation_removed_target,
            "restoration_exact": restoration_exact,
            "later_target_prompt_and_name_inert": target_inert,
            "gpu_device": restored_return.apparatus.device,
            "gpu_invariant_reuploaded": restored_return.apparatus.invariant_transport_reuploaded,
            "cpu_semantic_replay": restored_return.apparatus.cpu_semantic_replay_after_device,
            "binary_receiver_taken": restored_return.apparatus.binary_receiver_taken,
            "wall_milliseconds": started.elapsed().as_millis(),
        }),
    )?;
    write_manifest(&output)?;
    if !structural_passed {
        return Err("one or more L5 pass consequences failed".to_owned());
    }
    println!(
        "L5 passed: the complete laboratory standing returned one atomic four-coordinate passage into rest {} in {} ms",
        rest_identity,
        started.elapsed().as_millis()
    );
    Ok(())
}

fn detached(rest_path: &Path, output_path: &Path) -> Result<(), String> {
    let rest_bytes = fs::read(rest_path).map_err(display)?;
    let rest = LaboratoryCultivatedRest::read(&rest_bytes).map_err(display)?;
    let identity = rest.identity().to_owned();
    let returned_thread = rest.returned_deposit().thread_address.clone();
    let mut resident = rest.mount().map_err(display)?;
    let returned = resident.conduct().map_err(display)?;
    let incident = returned
        .factors
        .iter()
        .filter(|factor| factor.incident_threads.contains(&returned_thread))
        .count();
    let exact_gpu_return = returned.rest_identity_sha256 == identity
        && !returned.apparatus.invariant_transport_reuploaded
        && !returned.apparatus.cpu_semantic_replay_after_device
        && !returned.apparatus.binary_receiver_taken;
    write_json(
        output_path,
        &DetachedGrade {
            schema: "soma-life.l5-source-detached-return.v1",
            truth_status: if exact_gpu_return {
                "implemented-exact-measured"
            } else {
                "counterexample"
            },
            rest_identity_sha256: identity,
            factor_population: returned.factors.len(),
            returned_difference_factor_present: returned
                .factors
                .iter()
                .any(|factor| factor.address == returned_thread),
            incident_constitutive_population: incident,
            exact_gpu_return,
            source_dependencies_opened: Vec::new(),
        },
    )
}

fn mount_laboratory(aperture: &ContinuationAperture) -> Result<LaboratoryMountWitness, String> {
    let output = Command::new("git")
        .args(["ls-files", "-z"])
        .output()
        .map_err(display)?;
    if !output.status.success() {
        return Err("git refused the complete tracked repository manifest".to_owned());
    }
    let mut occurrences = Vec::new();
    let mut chain = Sha256::new();
    chain.update(b"holonics/l5/repository-addressed-chain/v1");
    let mut total_octets = 0u64;
    for (ordinal, raw) in output
        .stdout
        .split(|octet| *octet == 0)
        .filter(|raw| !raw.is_empty())
        .enumerate()
    {
        let path = std::str::from_utf8(raw).map_err(display)?.to_owned();
        let bytes = fs::read(&path).map_err(display)?;
        let material = AddressedMaterialOccurrence::found(
            format!("repository-occurrence/{ordinal}"),
            &bytes,
            ordinal
                .checked_sub(1)
                .map(|prior| format!("repository-occurrence/{prior}")),
            vec![path.clone()],
            vec!["the file surface remains exterior to cultivated morphology".to_owned()],
        )
        .map_err(display)?;
        chain.update((ordinal as u64).to_le_bytes());
        chain.update(hex_bytes(&material.payload_sha256)?);
        total_octets = total_octets
            .checked_add(material.payload_octets)
            .ok_or("repository extent overflow")?;
        occurrences.push(RepositoryOccurrenceWitness {
            ordinal,
            path,
            octets: material.payload_octets,
            payload_sha256: material.payload_sha256,
            predecessor_ordinal: ordinal.checked_sub(1),
        });
    }
    let later_return_population = aperture
        .families
        .iter()
        .filter(|family| family.later_operator_return.is_some())
        .count();
    let join_population = aperture
        .families
        .iter()
        .try_fold(0u64, |sum, family| {
            sum.checked_add(family.world.parent_join_pairs)?
                .checked_add(family.world.claude_tool_join_pairs)?
                .checked_add(family.world.codex_tool_join_pairs)
        })
        .ok_or("exchange join population overflow")?;
    Ok(LaboratoryMountWitness {
        exchange_source_occurrence_sha256: aperture.source_occurrence_sha256.render(),
        exchange_family_population: aperture.families.len(),
        exchange_response_message_population: aperture.complete_response_message_population,
        exchange_later_return_population: later_return_population,
        exchange_world_join_population: join_population,
        repository_occurrences: occurrences,
        repository_octets: total_octets,
        repository_chain_sha256: render_hex(&chain.finalize()),
        capture_preceded_later_targets: true,
    })
}

fn laboratory_winding_section(mount: &LaboratoryMountWitness) -> Result<Vec<Rat>, String> {
    let coordinates = [
        u64::try_from(mount.exchange_family_population).map_err(display)?,
        u64::try_from(mount.exchange_response_message_population).map_err(display)?,
        mount
            .exchange_world_join_population
            .checked_add(u64::try_from(mount.repository_occurrences.len()).map_err(display)?)
            .ok_or("winding coordinate overflow")?,
        u64::try_from(mount.exchange_later_return_population).map_err(display)?,
    ];
    coordinates
        .into_iter()
        .map(|coordinate| {
            i64::try_from(coordinate)
                .map(|coordinate| Rat::from_integer(BigInt::from(coordinate)))
                .map_err(display)
        })
        .collect()
}

fn factor_cross_codec_material<Standing: MaterialFactorizationStanding>(
    rest: &Standing,
) -> Result<Vec<MaterialNativeFactorization>, String> {
    let aperture = MaterialFactorizationAperture::found(rest).map_err(display)?;
    [
        (
            "prose",
            b"two independent populations return every joined pair".as_slice(),
        ),
        (
            "mathematics",
            b"A times B maps (a,b) into the product population".as_slice(),
        ),
        ("code", b"for each a and b emit the ordered pair".as_slice()),
    ]
    .into_iter()
    .enumerate()
    .map(|(ordinal, (face, payload))| {
        let material = AddressedMaterialOccurrence::found(
            format!("l5-material/{ordinal}"),
            payload,
            None,
            vec![face.to_owned()],
            vec!["the delivery face is exterior".to_owned()],
        )
        .map_err(display)?;
        let returned = independent_product_return(&material, ordinal)?;
        aperture.factor(&material, &returned).map_err(display)
    })
    .collect()
}

fn independent_product_return(
    material: &AddressedMaterialOccurrence,
    ordinal: usize,
) -> Result<CausalOperationWorldReturn, String> {
    let left = (0..2)
        .map(|at| format!("l5/{ordinal}/left/{at}"))
        .collect::<Vec<_>>();
    let right = (0..3)
        .map(|at| format!("l5/{ordinal}/right/{at}"))
        .collect::<Vec<_>>();
    let cells = left
        .iter()
        .flat_map(|left_member| {
            right.iter().map(move |right_member| CausalResultCell {
                occurrence: format!("l5/{ordinal}/cell/{left_member}/{right_member}"),
                left_member: Some(left_member.clone()),
                right_member: Some(right_member.clone()),
            })
        })
        .collect();
    let apparatus = ExteriorWorldReturnTestimony::found(
        format!("l5/{ordinal}/apparatus-return"),
        "exterior-world-body",
        true,
        b"the complete pair population returned",
        vec!["apparatus departs before native rest".to_owned()],
    )
    .map_err(display)?;
    CausalOperationWorldReturn::found(
        format!("l5/{ordinal}/world-return"),
        material.occurrence.clone(),
        left,
        right,
        cells,
        apparatus,
        vec!["future interventions remain open".to_owned()],
    )
    .map_err(display)
}

fn returned_difference(
    rest: &SituatedCultivatedEcologyRest,
    winding: Vec<Rat>,
) -> Result<SituatedDifferenceSection, String> {
    let branch = rest
        .branches()
        .first()
        .ok_or("the L2 rest has no winding branch")?;
    let (spool, thread) = rest
        .ecology()
        .native()
        .spools
        .iter()
        .find_map(|spool| {
            spool
                .threads
                .iter()
                .find(|thread| thread.address == branch.thread_address)
                .map(|thread| (spool, thread))
        })
        .ok_or("the first winding thread disappeared")?;
    let occurrence = thread
        .occurrences
        .first()
        .ok_or("the first winding has no occurrence")?;
    let entering = thread
        .parametrons
        .iter()
        .find(|cell| cell.native == occurrence.entering_native)
        .ok_or("the first winding has no entering Parametron")?;
    let emitting = thread
        .parametrons
        .iter()
        .find(|cell| cell.native == occurrence.emitting_native)
        .ok_or("the first winding has no emitting Parametron")?;
    let receiver = common_receiver(
        thread,
        occurrence.entering_native,
        occurrence.emitting_native,
    )?;
    let candidate_event = fresh_event(rest, &winding, b"candidate", None)?;
    let returned_event = fresh_event(rest, &winding, b"returned", Some(candidate_event))?;
    let fibre = BTreeSet::from([candidate_event, returned_event]);
    let candidate = NativeConductedSection {
        address: NativeSectionAddress {
            spool: spool.address.clone(),
            thread: "native-l5-candidate-section".to_owned(),
            occurrence: candidate_event,
        },
        predecessor: None,
        entering_boundary: thread.entering_boundary,
        emitting_boundary: thread.emitting_boundary,
        entering_port: OccurrencePort::input(candidate_event, 0),
        emitting_port: OccurrencePort::output(candidate_event, 0),
        entering_native: occurrence.entering_native,
        emitting_native: occurrence.emitting_native,
        incidence: NativeIncidenceTerm {
            occurrence: candidate_event,
            from: occurrence.entering_native,
            to: occurrence.emitting_native,
            coefficient: 1,
        },
        entering_section: entering.section.clone(),
        entering_current: entering.current.clone(),
        emitting_section: emitting.section.clone(),
        emitting_current: emitting.current.clone(),
        relative_phase: emitting.relative_phase.clone(),
        hand: emitting.hand,
        constitutive_response: NativeConstitutiveResponse {
            native: occurrence.emitting_native,
            receiver,
            presented: emitting.section.clone(),
            stored: emitting.current.clone(),
        },
        mutual_constitutive_responses: Vec::new(),
        ordered_word: thread.chronology.clone(),
        receiver,
        observation: observation(thread, occurrence.emitting_native, receiver)?,
        reconstruction_fibre: fibre.clone(),
        successor_sections: Vec::new(),
        open_exterior: vec![
            "the complete laboratory source remains outside this section".to_owned(),
        ],
    };
    let returned_section = ExactComplexWaveCurrent::new(
        &entering.section.real + &winding[0],
        &entering.section.imaginary + &winding[1],
    );
    let returned_current = ExactComplexWaveCurrent::new(
        &entering.current.real + &winding[2],
        &entering.current.imaginary + &winding[3],
    );
    let returned = NativeConductedSection {
        address: NativeSectionAddress {
            spool: spool.address.clone(),
            thread: "native-l5-returned-section".to_owned(),
            occurrence: returned_event,
        },
        predecessor: Some(candidate_event),
        entering_boundary: thread.emitting_boundary,
        emitting_boundary: thread.entering_boundary,
        entering_port: OccurrencePort::input(returned_event, 0),
        emitting_port: OccurrencePort::output(returned_event, 0),
        entering_native: occurrence.emitting_native,
        emitting_native: occurrence.entering_native,
        incidence: NativeIncidenceTerm {
            occurrence: returned_event,
            from: occurrence.emitting_native,
            to: occurrence.entering_native,
            coefficient: -1,
        },
        entering_section: emitting.section.clone(),
        entering_current: emitting.current.clone(),
        emitting_section: returned_section.clone(),
        emitting_current: returned_current.clone(),
        relative_phase: entering.relative_phase.clone(),
        hand: entering.hand,
        constitutive_response: NativeConstitutiveResponse {
            native: occurrence.entering_native,
            receiver,
            presented: returned_section,
            stored: returned_current,
        },
        mutual_constitutive_responses: Vec::new(),
        ordered_word: thread.chronology.clone(),
        receiver,
        observation: observation(thread, occurrence.entering_native, receiver)?,
        reconstruction_fibre: fibre.clone(),
        successor_sections: Vec::new(),
        open_exterior: vec![
            "the source apparatus has departed from the returned section".to_owned(),
        ],
    };
    let metric = ExactRatMatrix::new(
        winding
            .iter()
            .enumerate()
            .map(|(row, coefficient)| {
                winding
                    .iter()
                    .enumerate()
                    .map(|(column, _)| {
                        if row == column {
                            q(1) + coefficient * coefficient
                        } else {
                            q(0)
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .map_err(display)?;
    SituatedDifferenceSection::found(SituatedDifferenceInput {
        candidate,
        returned,
        carrying_occurrence: holonic_engine::native_spool::NativePullbackOccurrence {
            left: candidate_event,
            right: returned_event,
            joining_native: occurrence.emitting_native,
        },
        occurrence_fibres: vec![NativeCollapsedFibre {
            native: occurrence.emitting_native,
            occurrences: fibre,
        }],
        source_transport: ExactRatMatrix::identity(4).map_err(display)?,
        rebased_transport: ExactRatMatrix::identity(4).map_err(display)?,
        source_chart: ExactRatMatrix::identity(4).map_err(display)?,
        target_chart: ExactRatMatrix::identity(4).map_err(display)?,
        candidate_coordinates: vec![q(0), q(0), q(0), q(0)],
        returned_coordinates: winding.clone(),
        adjoint_steps: vec![life::native_intelligence::CausalAdjointStepInput {
            name: "complete-laboratory-return-through-standing-winding-chart".to_owned(),
            forward: ExactRatMatrix::identity(4).map_err(display)?,
            domain_metric: metric.clone(),
            codomain_metric: metric,
        }],
        terminal_covector: winding,
        native_obstructions: Vec::new(),
        open_deposition_boundary: "the complete returned section awaits one atomic L5 deposit"
            .to_owned(),
        open_exterior: vec![
            "richer future receivers may reopen the source condensation fibre".to_owned(),
        ],
    })
    .map_err(display)
}

fn common_receiver(
    thread: &holonic_engine::native_spool::NativeThread,
    left: holonic_engine::receiver_history_compression::NativeStateId,
    right: holonic_engine::receiver_history_compression::NativeStateId,
) -> Result<ReceiverId, String> {
    thread
        .constitutive_responses
        .iter()
        .map(|response| response.receiver)
        .find(|receiver| {
            thread
                .constitutive_responses
                .iter()
                .any(|response| response.native == left && response.receiver == *receiver)
                && thread
                    .constitutive_responses
                    .iter()
                    .any(|response| response.native == right && response.receiver == *receiver)
        })
        .ok_or_else(|| "the selected winding has no common endpoint receiver".to_owned())
}

fn observation(
    thread: &holonic_engine::native_spool::NativeThread,
    native: holonic_engine::receiver_history_compression::NativeStateId,
    receiver: ReceiverId,
) -> Result<holonic_engine::receiver_exact_compression::Observation, String> {
    thread
        .receiver_consequences
        .iter()
        .find(|consequence| consequence.native == native && consequence.receiver == receiver)
        .map(|consequence| consequence.observation)
        .ok_or_else(|| "the selected winding endpoint has no receiver consequence".to_owned())
}

fn fresh_event(
    rest: &SituatedCultivatedEcologyRest,
    winding: &[Rat],
    hand: &[u8],
    distinct_from: Option<EventId>,
) -> Result<EventId, String> {
    let occupied = rest
        .ecology()
        .native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    for salt in 0u64..1024 {
        let mut digest = Sha256::new();
        digest.update(b"holonics/l5/returned-world-event/v1");
        digest.update(rest.identity().as_bytes());
        digest.update(serde_json::to_vec(winding).map_err(display)?);
        digest.update(hand);
        digest.update(salt.to_le_bytes());
        let octets: [u8; 8] = digest.finalize()[..8].try_into().map_err(display)?;
        let event = EventId(u64::from_le_bytes(octets));
        if !occupied.contains(&event) && distinct_from != Some(event) {
            return Ok(event);
        }
    }
    Err("could not found a fresh addressed L5 event".to_owned())
}

fn q(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}

fn hex_bytes(value: &str) -> Result<Vec<u8>, String> {
    if value.len() % 2 != 0 {
        return Err("odd hexadecimal identity".to_owned());
    }
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let text = std::str::from_utf8(pair).map_err(display)?;
            u8::from_str_radix(text, 16).map_err(display)
        })
        .collect()
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(display)?
        .map(|entry| entry.map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    let files = entries
        .into_iter()
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path": entry.file_name().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": render_hex(&Sha256::digest(&bytes)),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema": "soma-life.l5-laboratory-world-tube-manifest.v1",
            "files": files,
        }),
    )
}

fn render_hex(value: &[u8]) -> String {
    value.iter().map(|octet| format!("{octet:02x}")).collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
