//! MEM3 receiver: the exact MEM2 contact is enacted as three causally dependent launches on one
//! resident card and read only after the outward boundary current has returned.

use std::{collections::BTreeSet, env, fs, path::PathBuf};

use holonic_engine::ExactComplexWaveCurrent;
use life::native_intelligence::{
    AdmittedAffineLaboratoryRestWitness, AffineLaboratoryCultivatedRest, FoundedInteriorContact,
    InteriorContactConsequence, NativeCausalMembrane, SharedSupportObstruction,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;

const REST: &str = concat!(
    "output/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const REST_WIRE_SHA256: &str = "026cbeba471ff00262b0ddc07596d602007fa3c672bb2ab96cafb3a5c0ff7fbc";
const REST_IDENTITY_SHA256: &str =
    "5b9a09396d0924ef1a5499737a1c609d943be38ec0647d394d35d79b7d460b2b";
const VALIDATION_RECEIPT_SHA256: &str =
    "c5220f4b1bfb52eb630f9b269f9688bd79ce35754f1eaa4fda3830faec4093e7";
const OUTPUT: &str = "output/the_athena_membrane_interior_returns_one_dependent_resident_word_mem3";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Mem3Grade {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    exact_host_receiver: FoundedInteriorContact,
    shared_resident_return: holonic_engine::cuda_refine::ResidentMembraneInteriorReturn,
    disjoint_host_obstruction: SharedSupportObstruction,
    disjoint_resident_return: holonic_engine::cuda_refine::ResidentMembraneInteriorReturn,
    shared_terminal_equals_predeclared_exact_receiver: bool,
    disjoint_terminal_is_exact_zero: bool,
    one_context: bool,
    two_real_device_dependency_edges_per_word: bool,
    one_terminal_synchronization_per_word: bool,
    zero_intermediate_host_egress: bool,
    zero_invariant_reupload: bool,
    zero_cpu_semantic_replay: bool,
    rest_identity_preserved: bool,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let witness = AdmittedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)?;
    let rest = AffineLaboratoryCultivatedRest::read_admitted(
        &fs::read(root.join(REST)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;
    let rested_identity = rest.identity().to_owned();
    let (left, shared, disjoint) = select_receiver_cells(rest.affine_cells())?;
    let mut membrane = NativeCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?;
    let InteriorContactConsequence::Founded(exact_host_receiver) = membrane
        .founded_interior_contact(&left, &shared)
        .map_err(display)?
    else {
        return Err("the predeclared shared receiver lost contact".to_owned());
    };
    let InteriorContactConsequence::Obstructed(disjoint_host_obstruction) = membrane
        .founded_interior_contact(&left, &disjoint)
        .map_err(display)?
    else {
        return Err("the predeclared disjoint receiver lost its obstruction".to_owned());
    };
    membrane = membrane.mount_resident_interior().map_err(display)?;
    let injected = ExactComplexWaveCurrent::new(rat(2), rat(3));
    let shared_resident_return = membrane
        .conduct_resident_interior(&left, &shared, &injected)
        .map_err(display)?;
    let disjoint_resident_return = membrane
        .conduct_resident_interior(&left, &disjoint, &injected)
        .map_err(display)?;
    let expected_terminal = exact_host_receiver.returned_response.multiply(&injected);
    let shared_terminal_equals_predeclared_exact_receiver = shared_resident_return.native_radiation
        == exact_host_receiver.returned_response
        && shared_resident_return.returned_radiation == expected_terminal;
    let disjoint_terminal_is_exact_zero = disjoint_resident_return
        .family_overlaps
        .iter()
        .all(|overlap| overlap == &rat(0))
        && disjoint_resident_return.native_radiation.is_zero()
        && disjoint_resident_return.returned_radiation.is_zero();
    let one_context =
        shared_resident_return.context_identity == disjoint_resident_return.context_identity;
    let two_real_device_dependency_edges_per_word =
        [&shared_resident_return, &disjoint_resident_return]
            .iter()
            .all(|returned| returned.launches == 3 && returned.device_dependency_edges == 2);
    let one_terminal_synchronization_per_word =
        [&shared_resident_return, &disjoint_resident_return]
            .iter()
            .all(|returned| returned.synchronizations == 1);
    let zero_intermediate_host_egress = [&shared_resident_return, &disjoint_resident_return]
        .iter()
        .all(|returned| returned.intermediate_host_egress_octets == 0);
    let zero_invariant_reupload = [&shared_resident_return, &disjoint_resident_return]
        .iter()
        .all(|returned| !returned.invariant_transport_reuploaded);
    let zero_cpu_semantic_replay = [&shared_resident_return, &disjoint_resident_return]
        .iter()
        .all(|returned| !returned.cpu_semantic_replay_after_device);
    let returned_rest = membrane.into_rest();
    let rest_identity_preserved = returned_rest.identity() == rested_identity;
    if !shared_terminal_equals_predeclared_exact_receiver
        || !disjoint_terminal_is_exact_zero
        || !one_context
        || !two_real_device_dependency_edges_per_word
        || !one_terminal_synchronization_per_word
        || !zero_intermediate_host_egress
        || !zero_invariant_reupload
        || !zero_cpu_semantic_replay
        || !rest_identity_preserved
    {
        return Err("the resident MEM3 word failed its exact receiver".to_owned());
    }
    let grade = Mem3Grade {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        exact_host_receiver,
        shared_resident_return,
        disjoint_host_obstruction,
        disjoint_resident_return,
        shared_terminal_equals_predeclared_exact_receiver,
        disjoint_terminal_is_exact_zero,
        one_context,
        two_real_device_dependency_edges_per_word,
        one_terminal_synchronization_per_word,
        zero_intermediate_host_egress,
        zero_invariant_reupload,
        zero_cpu_semantic_replay,
        rest_identity_preserved,
        open_exterior: vec![
            "MEM3 enacts the exact membrane interior on one card; durable returned morphology begins at MEM4"
                .to_owned(),
            "the cold exact comparison validates the terminal carrier and never selects or replays the hot device word"
                .to_owned(),
        ],
    };
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("00-dependent-resident-membrane-word.json"),
        serde_json::to_vec_pretty(&grade).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn select_receiver_cells(
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
    let disjoint = cells
        .iter()
        .skip(1)
        .find(|candidate| {
            candidate
                .landmark_factors
                .iter()
                .all(|factor| !support.contains(factor))
        })
        .ok_or_else(|| "no disjoint affine sibling remains as a control".to_owned())?;
    Ok((
        left.cell_address.clone(),
        shared.cell_address.clone(),
        disjoint.cell_address.clone(),
    ))
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
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
