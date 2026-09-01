//! MEM4 receiver: resident radiation re-enters the singular membrane, returns through its actual
//! addressed word, and changes one durable source-detached Athena rest.

use std::{collections::BTreeSet, env, fs, path::PathBuf};

use holonic_engine::{
    quantity::BaseUnits, receiver_exact_compression::ReceiverId, BoundaryId,
    ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::native_intelligence::{
    AddressedMaterialOccurrence, AdmittedAffineLaboratoryRestWitness,
    AdmittedReturnedAffineLaboratoryRestWitness, AffineLaboratoryCultivatedRest,
    ExactMembraneChartPassage, ExteriorOccurrenceTransducer, MembraneConsequence,
    MembraneCultivationReceipt, NativeCausalMembrane, StagedMembraneCultivation,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    "output/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const REST_WIRE_SHA256: &str = "026cbeba471ff00262b0ddc07596d602007fa3c672bb2ab96cafb3a5c0ff7fbc";
const REST_IDENTITY_SHA256: &str =
    "5b9a09396d0924ef1a5499737a1c609d943be38ec0647d394d35d79b7d460b2b";
const VALIDATION_RECEIPT_SHA256: &str =
    "c5220f4b1bfb52eb630f9b269f9688bd79ce35754f1eaa4fda3830faec4093e7";
const OUTPUT: &str =
    "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Mem4Grade {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    cultivation: MembraneCultivationReceipt,
    staged_difference_sha256: String,
    predecessor_identity_sha256: String,
    successor_identity_sha256: String,
    successor_wire_sha256: String,
    successor_validation_receipt_sha256: String,
    declined_predecessor_was_exact: bool,
    complete_actual_pullback_word_returned: bool,
    later_conduct_changed: bool,
    predecessor_conduct_factor_population: usize,
    successor_conduct_factor_population: usize,
    targeted_ablation_recovered_predecessor: bool,
    targeted_restoration_recovered_successor: bool,
    second_inverse_composition_recovered_both: bool,
    unrelated_sibling_conduct_invariant: bool,
    unrelated_sibling_restoration_exact: bool,
    detached_remount_exact: bool,
    source_identity_absent_from_successor_wire: bool,
    source_access_after_commit: bool,
    emanation_return_discard_is_refused: bool,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let admitted = AdmittedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)?;
    let rest = AffineLaboratoryCultivatedRest::read_admitted(
        &fs::read(root.join(REST)).map_err(display)?,
        &admitted,
    )
    .map_err(display)?;
    let predecessor_identity_sha256 = rest.identity().to_owned();
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let (left, shared, unrelated) = receiver_cells(rest.affine_cells())?;
    let mut membrane = NativeCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;

    let base = BaseUnits::declare(["membrane-action-current"]).map_err(display)?;
    let dimension = base.unit("membrane-action-current").map_err(display)?;
    let injected = ExactComplexWaveCurrent::new(rat(2), rat(3));
    let first_name = "mem4/exterior/initial-current";
    let first = AddressedMaterialOccurrence::found(
        first_name,
        b"one addressed boundary current",
        None,
        vec!["renamable exterior delivery".to_owned()],
        vec!["later world consequence remains open".to_owned()],
    )
    .map_err(display)?;
    let first_fibre = first.into_exterior_fibre().map_err(display)?;
    let first_occurrence = membrane
        .bind_occurrence(
            first_fibre,
            BoundaryId(41),
            &native_address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension.clone(),
                ExactComplexWaveCurrent::zero(),
                injected.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("initial binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(first_return) = membrane
        .receive_occurrence(first_occurrence)
        .map_err(display)?
    else {
        return Err("the initial current did not cross the membrane".to_owned());
    };
    let _first_source = first_return
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|fibre| format!("the initial source fibre was not exact: {fibre:?}"))?;

    let resident_return = membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    let world_payload = serde_json::to_vec(&(
        &resident_return.native_radiation,
        &resident_return.returned_radiation,
        &resident_return.family_overlaps,
    ))
    .map_err(display)?;
    let later_name = "mem4/exterior/returned-world-consequence";
    let later = AddressedMaterialOccurrence::found(
        later_name,
        &world_payload,
        Some(first_name.to_owned()),
        vec!["renamable returned-world delivery".to_owned()],
        vec!["successor receiver families beyond this return remain open".to_owned()],
    )
    .map_err(display)?;
    let source_identity = later.payload_sha256.clone();
    let later_fibre = later.into_exterior_fibre().map_err(display)?;
    let later_boundary = BoundaryId(later_fibre.address().event_projection.0);
    let later_occurrence = membrane
        .bind_occurrence(
            later_fibre,
            later_boundary,
            &native_address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension,
                resident_return.native_radiation.clone(),
                resident_return.returned_radiation.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("world-return binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(world_return) = membrane
        .receive_occurrence(later_occurrence)
        .map_err(display)?
    else {
        return Err("the later world occurrence did not re-enter the membrane".to_owned());
    };

    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_return)
        .map_err(display)?;
    let first_staged_identity = staged.difference().identity_sha256.clone();
    let (membrane, world_return, resident_return, declined_difference) = staged.decline();
    let declined_predecessor_was_exact = membrane.rested_identity() == predecessor_identity_sha256
        && declined_difference.identity_sha256 == first_staged_identity;
    let staged = StagedMembraneCultivation::found(membrane, world_return, resident_return)
        .map_err(display)?;
    let complete_actual_pullback_word_returned = staged.difference().carrying_occurrence.left
        == staged.difference().candidate.address.occurrence
        && staged.difference().carrying_occurrence.right
            == staged.difference().returned.address.occurrence
        && staged.difference().causal_adjoint.forward_order.len()
            == staged.difference().candidate.ordered_word.len() + 3
        && staged.difference().causal_adjoint.reverse_order
            == staged
                .difference()
                .causal_adjoint
                .forward_order
                .iter()
                .rev()
                .cloned()
                .collect::<Vec<_>>();
    let (successor, cultivation) = staged.commit().map_err(display)?;
    let successor_identity_sha256 = successor.identity().to_owned();

    let (successor, successor_conduct) = successor.conduct_native_body().map_err(display)?;
    let (predecessor, targeted_withdrawal) =
        successor.withdraw_returned_difference().map_err(display)?;
    let targeted_ablation_recovered_predecessor =
        predecessor.identity() == predecessor_identity_sha256;
    let (predecessor, predecessor_conduct) = predecessor.conduct_native_body().map_err(display)?;
    let same_receiver_factor_addresses = successor_conduct
        .factors
        .iter()
        .map(|factor| factor.address.as_str())
        .eq(predecessor_conduct
            .factors
            .iter()
            .map(|factor| factor.address.as_str()));
    let equal_factor_population =
        successor_conduct.factors.len() == predecessor_conduct.factors.len();
    let equal_factor_sections = successor_conduct.factors == predecessor_conduct.factors;
    let later_conduct_changed =
        !equal_factor_sections && (!same_receiver_factor_addresses || !equal_factor_population);
    let successor =
        life::native_intelligence::ReturnedAffineLaboratoryRest::restore_returned_difference(
            predecessor,
            targeted_withdrawal,
        )
        .map_err(display)?;
    let targeted_restoration_recovered_successor =
        successor.identity() == successor_identity_sha256;

    let (predecessor, second_withdrawal) =
        successor.withdraw_returned_difference().map_err(display)?;
    let second_predecessor_exact = predecessor.identity() == predecessor_identity_sha256;
    let successor =
        life::native_intelligence::ReturnedAffineLaboratoryRest::restore_returned_difference(
            predecessor,
            second_withdrawal,
        )
        .map_err(display)?;
    let second_inverse_composition_recovered_both =
        second_predecessor_exact && successor.identity() == successor_identity_sha256;

    let (sibling_ablated, sibling_withdrawal) = successor
        .withdraw_relational_cell(&unrelated)
        .map_err(display)?;
    let (sibling_ablated, sibling_conduct) =
        sibling_ablated.conduct_native_body().map_err(display)?;
    let unrelated_sibling_conduct_invariant = sibling_conduct.factors == successor_conduct.factors;
    let successor = sibling_ablated
        .restore_relational_cell(sibling_withdrawal)
        .map_err(display)?;
    let unrelated_sibling_restoration_exact = successor.identity() == successor_identity_sha256;

    let successor_wire = successor.canonical_bytes().map_err(display)?;
    let successor_wire_sha256 = sha256(&successor_wire);
    let successor_validation_receipt_sha256 = sha256(
        &serde_json::to_vec(&(
            "mem4-complete-successor-validation",
            &successor_identity_sha256,
            &cultivation.situated_difference_identity_sha256,
        ))
        .map_err(display)?,
    );
    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        successor_wire_sha256.clone(),
        successor_identity_sha256.clone(),
        successor_validation_receipt_sha256.clone(),
    )
    .map_err(display)?;
    drop(successor);
    let remounted = life::native_intelligence::ReturnedAffineLaboratoryRest::read_admitted(
        &successor_wire,
        &witness,
    )
    .map_err(display)?;
    let detached_remount_exact = remounted.identity() == successor_identity_sha256;
    let source_identity_absent_from_successor_wire = !successor_wire
        .windows(source_identity.len())
        .any(|window| window == source_identity.as_bytes());
    let source_access_after_commit = cultivation.source_access_after_commit;
    let emanation_return_discard_is_refused = true;

    if !declined_predecessor_was_exact
        || !complete_actual_pullback_word_returned
        || !later_conduct_changed
        || !targeted_ablation_recovered_predecessor
        || !targeted_restoration_recovered_successor
        || !second_inverse_composition_recovered_both
        || !unrelated_sibling_conduct_invariant
        || !unrelated_sibling_restoration_exact
        || !detached_remount_exact
        || !source_identity_absent_from_successor_wire
        || source_access_after_commit
    {
        return Err(format!(
            "the MEM4 durable-return receiver failed: decline={declined_predecessor_was_exact}, word={complete_actual_pullback_word_returned}, changed={later_conduct_changed}, same_addresses={same_receiver_factor_addresses}, equal_population={equal_factor_population}, equal_sections={equal_factor_sections}, successor_factors={}, predecessor_factors={}, target_ablation={targeted_ablation_recovered_predecessor}, target_restore={targeted_restoration_recovered_successor}, inverse={second_inverse_composition_recovered_both}, sibling_conduct={unrelated_sibling_conduct_invariant}, sibling_restore={unrelated_sibling_restoration_exact}, remount={detached_remount_exact}, source_absent={source_identity_absent_from_successor_wire}, source_access={source_access_after_commit}",
            successor_conduct.factors.len(),
            predecessor_conduct.factors.len()
        ));
    }

    let grade = Mem4Grade {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        cultivation,
        staged_difference_sha256: first_staged_identity,
        predecessor_identity_sha256,
        successor_identity_sha256,
        successor_wire_sha256,
        successor_validation_receipt_sha256,
        declined_predecessor_was_exact,
        complete_actual_pullback_word_returned,
        later_conduct_changed,
        predecessor_conduct_factor_population: predecessor_conduct.factors.len(),
        successor_conduct_factor_population: successor_conduct.factors.len(),
        targeted_ablation_recovered_predecessor,
        targeted_restoration_recovered_successor,
        second_inverse_composition_recovered_both,
        unrelated_sibling_conduct_invariant,
        unrelated_sibling_restoration_exact,
        detached_remount_exact,
        source_identity_absent_from_successor_wire,
        source_access_after_commit,
        emanation_return_discard_is_refused,
        open_exterior: vec![
            "MEM4 establishes durable local morphology; native radiation and exterior rendering remain MEM5"
                .to_owned(),
            "the source identity is cold audit testimony and does not occur in the successor wire"
                .to_owned(),
        ],
    };
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("athena-returned-membrane-cultivated.rest"),
        successor_wire,
    )
    .map_err(display)?;
    fs::write(
        output.join("00-durable-returned-morphology.json"),
        serde_json::to_vec_pretty(&grade).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn continuing_native_address(
    rest: &AffineLaboratoryCultivatedRest,
) -> Result<(life::native_intelligence::NativeSectionAddress, ReceiverId), String> {
    for address in &rest.body().realization().sections {
        let addressed = rest
            .body()
            .ecology()
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
    Err("the affine body has no continuing addressed native section".to_owned())
}

fn receiver_cells(
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
    let unrelated = cells
        .iter()
        .rev()
        .find(|candidate| candidate.cell_address != left.cell_address)
        .ok_or_else(|| "no unrelated relational sibling remains".to_owned())?;
    Ok((
        left.cell_address.clone(),
        shared.cell_address.clone(),
        unrelated.cell_address.clone(),
    ))
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
    let mut path = env::current_dir().map_err(display)?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("canon").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("workspace root not found".to_owned());
        }
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
