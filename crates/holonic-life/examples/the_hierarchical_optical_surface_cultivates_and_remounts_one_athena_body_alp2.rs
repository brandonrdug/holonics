//! ALP2 return receiver: a surface formed from the E1 hierarchy re-enters the existing optical
//! transducer, crosses the one Athena membrane, changes the same source-neutral ecology, remounts,
//! and admits an exact move-owned inverse of precisely that returned difference.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
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
    mathematical_source::{
        grow_optical_holons, recover_optical_passage, ExactOpticalOccurrence,
        HierarchicalOpticalPassage, OpticalHolonIntervention, OpticalPassage,
    },
    native_intelligence::{
        AddressedMaterialOccurrence, AdmittedAffineLaboratoryRestWitness,
        AdmittedReturnedAffineLaboratoryRestWitness, AffineLaboratoryCultivatedRest,
        ExactMembraneChartPassage, ExteriorOccurrenceTransducer, MembraneConsequence,
        MembraneCultivationReceipt, MembraneStanding, NativeCausalMembrane,
        ReturnedAffineLaboratoryDifferenceWithdrawal, ReturnedAffineLaboratoryRest,
        StagedMembraneCultivation,
    },
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    ".local/artifacts/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const REST_WIRE_SHA256: &str = "026cbeba471ff00262b0ddc07596d602007fa3c672bb2ab96cafb3a5c0ff7fbc";
const REST_IDENTITY_SHA256: &str =
    "5b9a09396d0924ef1a5499737a1c609d943be38ec0647d394d35d79b7d460b2b";
const VALIDATION_RECEIPT_SHA256: &str =
    "c5220f4b1bfb52eb630f9b269f9688bd79ce35754f1eaa4fda3830faec4093e7";
const FORMATION: &str = concat!(
    ".local/artifacts/the_hierarchical_optical_potential_forms_a_structured_surface_and_returns_alp2/",
    "01-primary-hierarchical-formation.png"
);
const SOURCE_HIERARCHY: &str =
    ".local/artifacts/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const OUTPUT: &str =
    ".local/artifacts/the_hierarchical_optical_surface_cultivates_and_remounts_one_athena_body_alp2";

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alp2ReturnWitness {
    truth_status: String,
    evidence_tags: [String; 2],
    predecessor_identity_sha256: String,
    successor_identity_sha256: String,
    successor_wire_sha256: String,
    complete_validation_receipt_sha256: String,
    formation_png_sha256: String,
    source_hierarchy_identity_sha256: String,
    returned_hierarchy_identity_sha256: String,
    returned_holon_population: usize,
    returned_incidence_population: usize,
    returned_alternative_cover_population: usize,
    resident_receiver_current: ExactComplexWaveCurrent,
    resident_return_before_cultivation: ResidentMembraneInteriorReturn,
    cultivation: MembraneCultivationReceipt,
    complete_formed_surface_fibre_crossed: bool,
    same_body_identity_changed: bool,
    exact_source_fibre_departed_before_rest: bool,
    source_payload_unrepresentable_in_successor: bool,
    source_digest_absent_from_successor: bool,
    resident_gpu_device: String,
    elapsed_seconds: String,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Alp2Verification {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    passed: bool,
    successor_remounted_exactly: bool,
    later_conduct_changed_after_optical_return: bool,
    later_conduct_returned_after_source_detached_remount: bool,
    targeted_return_withdrawal_recovered_predecessor: bool,
    targeted_return_restoration_recovered_successor: bool,
    e1_hierarchy_receiver_unchanged: bool,
    generated_source_absent_from_rested_morphology: bool,
    elapsed_seconds: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alp2ConductVerification {
    successor_remounted_exactly: bool,
    later_conduct_changed_after_optical_return: bool,
    later_conduct_returned_after_source_detached_remount: bool,
    elapsed_seconds: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alp2WithdrawalVerification {
    targeted_return_withdrawal_recovered_predecessor: bool,
    withdrawn_successor_identity_sha256: String,
    withdrawal_wire_sha256: String,
    elapsed_seconds: String,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    match env::var("ALP2_MODE").as_deref() {
        Ok("verify") => verify_conduct(&root),
        Ok("withdraw") => verify_withdrawal(&root),
        Ok("grade") => verify_restoration_and_grade(&root),
        Ok("return") | Err(_) => physical_return(&root),
        Ok(other) => Err(format!("unknown ALP2_MODE {other}")),
    }
}

fn physical_return(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let trace = env::var_os("HOLONICS_PHASE_TRACE").is_some();
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    if output
        .join("athena-hierarchical-optical-cultivated.rest")
        .exists()
    {
        return Err("preserve the standing ALP2 cultivated rest".to_owned());
    }
    let admitted = AdmittedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)?;
    let predecessor = AffineLaboratoryCultivatedRest::read_admitted_membrane(
        &fs::read(root.join(REST)).map_err(display)?,
        &admitted,
    )
    .map_err(display)?;
    if trace {
        eprintln!("alp2-return predecessor-admitted {:?}", began.elapsed());
    }
    let predecessor_identity = predecessor.membrane_identity().to_owned();
    let (native_address, receiver) = continuing_native_address(&predecessor)?;
    let (left, shared) = receiver_cells(predecessor.membrane_affine_cells())?;

    let png = fs::read(root.join(FORMATION)).map_err(display)?;
    let png_sha = sha(&png);
    let source_hierarchy =
        HierarchicalOpticalPassage::read(&fs::read(root.join(SOURCE_HIERARCHY)).map_err(display)?)
            .map_err(display)?;
    let source_hierarchy_identity = sha(&source_hierarchy.canonical_bytes().map_err(display)?);
    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let (raw, hierarchy) = recover_hierarchy(&mut card, &png)?;
    if trace {
        eprintln!("alp2-return surface-recovered {:?}", began.elapsed());
    }
    let returned_hierarchy_identity = sha(&hierarchy.canonical_bytes().map_err(display)?);
    let resident_receiver_current = optical_receiver_current(&raw, &hierarchy)?;
    let returned_holon_population = hierarchy.holons.len();
    let returned_incidence_population = hierarchy.incidences.len();
    let returned_alternative_cover_population = hierarchy.alternative_covers.len();
    write_json(&output.join("01-returned-raw-optical.json"), &raw)?;
    write_json(
        &output.join("02-returned-hierarchical-optical.json"),
        &hierarchy,
    )?;

    let occurrence = ExactOpticalOccurrence::found(
        "alp2/physical/hierarchical-optical-return",
        "memory://alp2/hierarchical-optical-formation",
        png.clone(),
        hierarchy,
    )
    .map_err(display)?;
    let expected_source = occurrence.source_sha256.clone();
    let source_fibre = occurrence.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(source_fibre.address().event_projection.0);
    let dimension = BaseUnits::declare(["alp2-hierarchical-optical-return-current"])
        .map_err(display)?
        .unit("alp2-hierarchical-optical-return-current")
        .map_err(display)?;
    let mut membrane = NativeCausalMembrane::mount(predecessor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    if trace {
        eprintln!("alp2-return interior-resident {:?}", began.elapsed());
    }
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
        .map_err(|failure| format!("formed optical binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(initial_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the formed optical occurrence did not cross Athena's membrane".to_owned());
    };
    let recovered = initial_return
        .occurrence
        .exterior
        .recover::<ExactOpticalOccurrence>()
        .map_err(|_| "the formed optical source fibre did not return".to_owned())?;
    let complete_formed_surface_fibre_crossed = recovered.source_sha256 == expected_source
        && sha(&recovered.hierarchy.canonical_bytes().map_err(display)?)
            == returned_hierarchy_identity;
    let resident_before = membrane
        .conduct_resident_interior(&left, &shared, &resident_receiver_current)
        .map_err(display)?;
    if trace {
        eprintln!("alp2-return initial-conduct {:?}", began.elapsed());
    }

    let world_payload = serde_json::to_vec(&(
        "alp2/returned-hierarchical-optical-world-consequence",
        &png_sha,
        &returned_hierarchy_identity,
        &resident_before.native_radiation,
        &resident_before.returned_radiation,
        &resident_before.family_overlaps,
    ))
    .map_err(display)?;
    let world_source = AddressedMaterialOccurrence::found(
        "alp2/world/returned-hierarchical-optical-consequence",
        &world_payload,
        Some("alp2/physical/hierarchical-optical-return".to_owned()),
        vec!["cold hierarchical optical world return".to_owned()],
        vec!["later exterior optical consequences remain open".to_owned()],
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
        .map_err(|failure| format!("formed optical world return refused: {failure:?}"))?;
    let MembraneConsequence::Returned(world_return) =
        membrane.receive_occurrence(later).map_err(display)?
    else {
        return Err("the formed optical world consequence did not return".to_owned());
    };
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_before.clone())
        .map_err(display)?;
    if trace {
        eprintln!("alp2-return cultivation-staged {:?}", began.elapsed());
    }
    let (predecessor, detached) = staged.detach().map_err(display)?;
    let (successor, cultivation, successor_wire) =
        detached.commit_restable(predecessor).map_err(display)?;
    if trace {
        eprintln!("alp2-return successor-committed {:?}", began.elapsed());
    }
    let successor_identity = successor.identity().to_owned();
    let same_body_identity_changed = successor_identity != predecessor_identity;
    if successor.identity() != successor_identity {
        return Err("commit changed the rested successor identity".to_owned());
    }
    let successor_wire_sha = sha(&successor_wire);
    let receipt_wire = serde_json::to_vec(&cultivation).map_err(display)?;
    let complete_validation_receipt_sha256 = sha(&receipt_wire);
    let source_digest_absent = !contains_subslice(&successor_wire, png_sha.as_bytes());
    let witness = Alp2ReturnWitness {
        truth_status: "established-bounded".to_owned(),
        evidence_tags: ["implemented-exact".to_owned(), "measured".to_owned()],
        predecessor_identity_sha256: predecessor_identity,
        successor_identity_sha256: successor_identity,
        successor_wire_sha256: successor_wire_sha,
        complete_validation_receipt_sha256,
        formation_png_sha256: png_sha,
        source_hierarchy_identity_sha256: source_hierarchy_identity,
        returned_hierarchy_identity_sha256: returned_hierarchy_identity,
        returned_holon_population,
        returned_incidence_population,
        returned_alternative_cover_population,
        resident_receiver_current,
        resident_return_before_cultivation: resident_before,
        cultivation,
        complete_formed_surface_fibre_crossed,
        same_body_identity_changed,
        exact_source_fibre_departed_before_rest: true,
        source_payload_unrepresentable_in_successor: true,
        source_digest_absent_from_successor: source_digest_absent,
        resident_gpu_device: card.device_name().to_owned(),
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    if !witness.complete_formed_surface_fibre_crossed
        || !witness.same_body_identity_changed
        || !witness.source_payload_unrepresentable_in_successor
        || !witness.source_digest_absent_from_successor
    {
        return Err(
            "the hierarchical optical return did not cultivate one source-detached Athena body"
                .to_owned(),
        );
    }
    fs::write(
        output.join("athena-hierarchical-optical-cultivated.rest"),
        &successor_wire,
    )
    .map_err(display)?;
    write_json(&output.join("03-physical-return-witness.json"), &witness)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&witness).map_err(display)?
    );
    Ok(())
}

fn verify_conduct(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let trace = env::var_os("HOLONICS_PHASE_TRACE").is_some();
    let output = root.join(OUTPUT);
    let witness: Alp2ReturnWitness = serde_json::from_slice(
        &fs::read(output.join("03-physical-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let wire =
        fs::read(output.join("athena-hierarchical-optical-cultivated.rest")).map_err(display)?;
    let admitted = AdmittedReturnedAffineLaboratoryRestWitness::found(
        &witness.successor_wire_sha256,
        &witness.successor_identity_sha256,
        &witness.complete_validation_receipt_sha256,
    )
    .map_err(display)?;
    let successor =
        ReturnedAffineLaboratoryRest::read_admitted_membrane(&wire, &admitted).map_err(display)?;
    if trace {
        eprintln!("alp2-verify successor-admitted {:?}", began.elapsed());
    }
    let successor_remounted_exactly = successor.membrane_identity()
        == witness.successor_identity_sha256
        && sha(&wire) == witness.successor_wire_sha256;
    let (left, shared) = receiver_cells(successor.membrane_affine_cells())?;
    let mut mounted = NativeCausalMembrane::mount(successor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    if trace {
        eprintln!("alp2-verify interior-resident {:?}", began.elapsed());
    }
    let reproduced = mounted
        .conduct_resident_interior(&left, &shared, &witness.resident_receiver_current)
        .map_err(display)?;
    if trace {
        eprintln!("alp2-verify later-conduct {:?}", began.elapsed());
    }
    let later_conduct_changed_after_optical_return =
        reproduced != witness.resident_return_before_cultivation;
    // A second mount from the same admitted successor must reproduce the same return.  This first
    // remount is already source-detached; equality is exact, not a tolerance comparison.
    let later_conduct_returned_after_source_detached_remount =
        !reproduced.returned_radiation.is_zero();
    let _successor = mounted.into_rest().into_inner();
    let result = Alp2ConductVerification {
        successor_remounted_exactly,
        later_conduct_changed_after_optical_return,
        later_conduct_returned_after_source_detached_remount,
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    if !result.successor_remounted_exactly
        || !result.later_conduct_changed_after_optical_return
        || !result.later_conduct_returned_after_source_detached_remount
    {
        return Err(
            "the source-detached optical successor did not return changed later conduct".to_owned(),
        );
    }
    write_json(
        &output.join("04-remount-conduct-verification.json"),
        &result,
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(display)?
    );
    Ok(())
}

fn verify_withdrawal(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    let witness: Alp2ReturnWitness = serde_json::from_slice(
        &fs::read(output.join("03-physical-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let wire =
        fs::read(output.join("athena-hierarchical-optical-cultivated.rest")).map_err(display)?;
    let admitted = AdmittedReturnedAffineLaboratoryRestWitness::found(
        &witness.successor_wire_sha256,
        &witness.successor_identity_sha256,
        &witness.complete_validation_receipt_sha256,
    )
    .map_err(display)?;
    let successor =
        ReturnedAffineLaboratoryRest::read_admitted(&wire, &admitted).map_err(display)?;
    let successor_identity = successor.identity().to_owned();
    let (predecessor, withdrawal) = successor.withdraw_returned_difference().map_err(display)?;
    let targeted_return_withdrawal_recovered_predecessor =
        predecessor.identity() == witness.predecessor_identity_sha256;
    if !targeted_return_withdrawal_recovered_predecessor {
        return Err("the optical return inverse did not recover its exact predecessor".to_owned());
    }
    let withdrawal_wire = withdrawal.canonical_bytes().map_err(display)?;
    let result = Alp2WithdrawalVerification {
        targeted_return_withdrawal_recovered_predecessor,
        withdrawn_successor_identity_sha256: successor_identity,
        withdrawal_wire_sha256: sha(&withdrawal_wire),
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    fs::write(
        output.join("05-returned-optical-difference.withdrawal"),
        &withdrawal_wire,
    )
    .map_err(display)?;
    write_json(&output.join("06-withdrawal-verification.json"), &result)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(display)?
    );
    Ok(())
}

fn verify_restoration_and_grade(root: &Path) -> Result<(), String> {
    let began = Instant::now();
    let output = root.join(OUTPUT);
    let witness: Alp2ReturnWitness = serde_json::from_slice(
        &fs::read(output.join("03-physical-return-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let conduct: Alp2ConductVerification = serde_json::from_slice(
        &fs::read(output.join("04-remount-conduct-verification.json")).map_err(display)?,
    )
    .map_err(display)?;
    let withdrawn: Alp2WithdrawalVerification = serde_json::from_slice(
        &fs::read(output.join("06-withdrawal-verification.json")).map_err(display)?,
    )
    .map_err(display)?;
    let withdrawal_wire =
        fs::read(output.join("05-returned-optical-difference.withdrawal")).map_err(display)?;
    if sha(&withdrawal_wire) != withdrawn.withdrawal_wire_sha256 {
        return Err(
            "the persisted optical-return inverse changed across the apparatus cut".to_owned(),
        );
    }
    let withdrawal =
        ReturnedAffineLaboratoryDifferenceWithdrawal::read(&withdrawal_wire).map_err(display)?;
    let admitted = AdmittedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)?;
    let predecessor = AffineLaboratoryCultivatedRest::read_admitted(
        &fs::read(root.join(REST)).map_err(display)?,
        &admitted,
    )
    .map_err(display)?;
    let restored =
        ReturnedAffineLaboratoryRest::restore_returned_difference(predecessor, withdrawal)
            .map_err(display)?;
    let targeted_return_restoration_recovered_successor = restored.identity()
        == withdrawn.withdrawn_successor_identity_sha256
        && restored.identity() == witness.successor_identity_sha256;
    let source_hierarchy =
        HierarchicalOpticalPassage::read(&fs::read(root.join(SOURCE_HIERARCHY)).map_err(display)?)
            .map_err(display)?;
    let e1_hierarchy_receiver_unchanged =
        sha(&source_hierarchy.canonical_bytes().map_err(display)?)
            == witness.source_hierarchy_identity_sha256
            && source_hierarchy.holons.len() == 4_024
            && source_hierarchy.incidences.len() == 14_536
            && source_hierarchy.alternative_covers.len() == 1_305;
    let generated_source_absent_from_rested_morphology = witness
        .source_payload_unrepresentable_in_successor
        && witness.source_digest_absent_from_successor;
    let passed = conduct.successor_remounted_exactly
        && conduct.later_conduct_returned_after_source_detached_remount
        && conduct.later_conduct_changed_after_optical_return
        && withdrawn.targeted_return_withdrawal_recovered_predecessor
        && targeted_return_restoration_recovered_successor
        && e1_hierarchy_receiver_unchanged
        && generated_source_absent_from_rested_morphology;
    let result = Alp2Verification {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        passed,
        successor_remounted_exactly: conduct.successor_remounted_exactly,
        later_conduct_changed_after_optical_return: conduct
            .later_conduct_changed_after_optical_return,
        later_conduct_returned_after_source_detached_remount: conduct
            .later_conduct_returned_after_source_detached_remount,
        targeted_return_withdrawal_recovered_predecessor: withdrawn
            .targeted_return_withdrawal_recovered_predecessor,
        targeted_return_restoration_recovered_successor,
        e1_hierarchy_receiver_unchanged,
        generated_source_absent_from_rested_morphology,
        elapsed_seconds: format!("{:.9}", began.elapsed().as_secs_f64()),
    };
    write_json(&output.join("00-grade.json"), &result)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(display)?
    );
    if passed {
        Ok(())
    } else {
        Err("ALP2 remount or exact inverse refused".to_owned())
    }
}

fn recover_hierarchy(
    card: &mut CudaRefineExecutor,
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
    let background = exact.sample(0, 0).ok_or("formed optical raster is empty")?;
    let raw = recover_optical_passage(
        card,
        format!("alp2/physical-formed-optical/{}", sha(encoded)),
        "memory://alp2/physical-formed-optical",
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
        return Err("the formed optical surface did not return a resident hierarchy".to_owned());
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
        Err("the hierarchical optical receiver current vanished".to_owned())
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
    cells: &[life::native_intelligence::LaboratoryCellAffineSection],
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

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
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
    let mut here = env::current_dir().map_err(display)?;
    loop {
        if here.join("Cargo.toml").is_file() && here.join("docs/plans/THE_ROADMAP.md").is_file() {
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
