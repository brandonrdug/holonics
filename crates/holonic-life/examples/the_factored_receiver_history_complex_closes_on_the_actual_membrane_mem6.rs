//! MEM6's narrow production-carrier gate on the actual seam-bearing Athena body.
//!
//! The apparatus supplies one unchanged exterior occurrence, invokes the standing resident owner,
//! and records its comparison with the cold direct restriction witness.  All contraction,
//! generator action, phase return and balance remain in source owners.

use std::{fs, path::PathBuf};

use life::native_intelligence::{
    AdmittedReturnedAffineLaboratoryRestWitness, FactoredReceiverHistoryGateReceipt,
    GranularCultivationWithdrawal, GranularReturnedAffineEcologyRest, NativeCausalMembrane,
    ReturnedAffineLaboratoryRest,
};
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    ".local/artifacts/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
    "athena-returned-membrane-cultivated.rest"
);
const ORGAN: &str = concat!(
    ".local/artifacts/the_causal_boundary_ports_cultivate_one_athena_successor_with_exact_projective_factor_currents_mem6/",
    "athena-causal-boundary-organ.rest"
);
const OUTPUT: &str =
    ".local/artifacts/the_factored_receiver_history_complex_closes_on_the_actual_membrane_mem6";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct GateReturn {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    successor_identity_sha256: String,
    receipt: FactoredReceiverHistoryGateReceipt,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output)?;
    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
        "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
        "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
    )?;
    let predecessor =
        ReturnedAffineLaboratoryRest::read_admitted(&fs::read(root.join(PREDECESSOR))?, &witness)?;
    let withdrawal = GranularCultivationWithdrawal::read(&fs::read(root.join(ORGAN))?)?;
    let successor = GranularReturnedAffineEcologyRest::restore(predecessor, withdrawal)?;
    let successor_identity_sha256 = successor.identity().to_owned();
    let mut membrane = NativeCausalMembrane::mount(successor)
        .constitute_interior()?
        .mount_resident_interior()?
        .mount_resident_factor_receiver_faces()?;
    let receipt = membrane.verify_factored_receiver_history_occurrence(
        "mem6/request/describe",
        b"Describe Brandon.",
    )?;
    let returned = GateReturn {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        successor_identity_sha256,
        receipt,
    };
    fs::write(
        output.join("receiver-history-gate.json"),
        serde_json::to_vec_pretty(&returned)?,
    )?;
    Ok(())
}
