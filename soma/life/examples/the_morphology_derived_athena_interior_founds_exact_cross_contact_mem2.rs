//! MEM2 receiver: one cultivated Athena body derives its sheaf, founds one exact local contact,
//! and refuses a disjoint sibling without smoothing across the absent support.

use std::{collections::BTreeSet, env, fs, path::PathBuf};

use life::athena_native::{
    AdmittedAffineLaboratoryRestWitness, AffineLaboratoryCultivatedAthenaRest,
    AthenaCausalMembrane, FoundedInteriorContact, InteriorConstitutionReceipt,
    InteriorContactConsequence, SharedSupportObstruction,
};
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
const OUTPUT: &str =
    "output/the_morphology_derived_athena_interior_founds_exact_cross_contact_mem2";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Mem2Grade {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    constitution: InteriorConstitutionReceipt,
    founded_cross_contact: FoundedInteriorContact,
    disjoint_sibling: SharedSupportObstruction,
    same_move_owned_rest_returned: bool,
    conservation_balance_returned_exactly: bool,
    reorientation_covariance_returned_exactly: bool,
    nonzero_cross_contact_returned: bool,
    disjoint_sibling_returned_zero: bool,
    exact_kernel_radical_fibre_returned: bool,
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
    let rest = AffineLaboratoryCultivatedAthenaRest::read_admitted(
        &fs::read(root.join(REST)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;
    let rested_identity = rest.identity().to_owned();
    let (left, shared, disjoint) = select_receiver_cells(rest.affine_cells())?;
    let membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?;
    let constitution = membrane
        .interior()
        .ok_or_else(|| "the exact membrane interior was not retained".to_owned())?
        .receipt()
        .clone();
    let InteriorContactConsequence::Founded(founded) = membrane
        .founded_interior_contact(&left, &shared)
        .map_err(display)?
    else {
        return Err("the shared affine sections did not found contact".to_owned());
    };
    let InteriorContactConsequence::Obstructed(obstructed) = membrane
        .founded_interior_contact(&left, &disjoint)
        .map_err(display)?
    else {
        return Err("the disjoint affine sibling was indiscriminately smoothed".to_owned());
    };
    let conservation_balance_returned_exactly = founded.exact_exchange_balance.is_zero();
    let reorientation_covariance_returned_exactly = founded.capacity_weighted_overlap
        == founded.simultaneously_reoriented_overlap
        && founded.returned_response == founded.simultaneously_reoriented_response;
    let nonzero_cross_contact_returned = !founded.returned_response.is_zero();
    let disjoint_sibling_returned_zero = obstructed.returned_response.is_zero();
    let exact_kernel_radical_fibre_returned =
        founded.reconstruction_fibre.functional_on_hidden_difference
            == num_rational::BigRational::from_integer(0.into())
            && !founded.reconstruction_fibre.radical.is_empty();
    let returned_rest = membrane.into_rest();
    let same_move_owned_rest_returned = returned_rest.identity() == rested_identity;
    if !conservation_balance_returned_exactly
        || !reorientation_covariance_returned_exactly
        || !nonzero_cross_contact_returned
        || !disjoint_sibling_returned_zero
        || !exact_kernel_radical_fibre_returned
        || !same_move_owned_rest_returned
    {
        return Err("the exact MEM2 return failed its declared receiver".to_owned());
    }
    let grade = Mem2Grade {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        constitution,
        founded_cross_contact: founded,
        disjoint_sibling: obstructed,
        same_move_owned_rest_returned,
        conservation_balance_returned_exactly,
        reorientation_covariance_returned_exactly,
        nonzero_cross_contact_returned,
        disjoint_sibling_returned_zero,
        exact_kernel_radical_fibre_returned,
        open_exterior: vec![
            "MEM2 establishes the exact interior law; one device-resident interacting word begins at MEM3"
                .to_owned(),
            "no durable returned morphology or inferred exterior response is claimed at MEM2"
                .to_owned(),
        ],
    };
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("00-morphology-derived-interior.json"),
        serde_json::to_vec_pretty(&grade).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn select_receiver_cells(
    cells: &[life::athena_native::LaboratoryCellAffineSection],
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
