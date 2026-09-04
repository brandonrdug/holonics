use std::{env, error::Error, fs, path::PathBuf};

use life::native_intelligence::SourceNeutralEcologyRest;
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    ".local/artifacts/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0/",
    "athena-source-neutral.rest"
);
const OUTPUT: &str = concat!(
    ".local/artifacts/",
    "the_complete_factor_current_meets_the_winding_constitutive_chart_uar3"
);

#[derive(Serialize)]
struct Uar3D0Audit {
    truth_status: &'static str,
    rest_identity_sha256: String,
    chart_identity_sha256: String,
    receiver_history_compression_identity_sha256: String,
    factor_population: usize,
    winding_population: usize,
    rank: usize,
    kernel_dimension: usize,
    total_factor_coverage: bool,
    orientation_covariant: bool,
    receiver_history_fibres_singleton: bool,
    q_descent_complete: bool,
    complete_factor_reconstruction_fibre_retained: bool,
    exterior_occurrence_consulted: bool,
    every_branch_current_nonzero: bool,
    every_branch_identity_distinct: bool,
}

fn main() -> Result<(), Box<dyn Error>> {
    let root = repository_root()?;
    let output = env::var_os("HOLONICS_OUTPUT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join(OUTPUT));
    fs::create_dir_all(&output)?;

    let rest = SourceNeutralEcologyRest::read(&fs::read(root.join(PREDECESSOR))?)?;
    let rest_identity_sha256 = rest.identity().to_owned();
    let resident = rest.mount_resident()?;
    let chart = resident.factor_winding_constitutive_chart()?;
    let every_branch_current_nonzero = chart
        .branch_functionals
        .iter()
        .all(|branch| !branch.constitutive_current.is_zero());
    let every_branch_identity_distinct = chart
        .branch_functionals
        .iter()
        .map(|branch| &branch.identity_sha256)
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        == chart.branch_functionals.len();
    let audit = Uar3D0Audit {
        truth_status: "implemented-exact; measured",
        rest_identity_sha256,
        chart_identity_sha256: chart.identity_sha256.clone(),
        receiver_history_compression_identity_sha256: chart
            .receiver_history_compression_identity_sha256
            .clone(),
        factor_population: chart.factor_native_addresses.len(),
        winding_population: chart.branch_functionals.len(),
        rank: chart.rank,
        kernel_dimension: chart.kernel_dimension,
        total_factor_coverage: chart.total_factor_coverage,
        orientation_covariant: chart.orientation_covariant,
        receiver_history_fibres_singleton: chart.receiver_history_fibres_singleton,
        q_descent_complete: chart.q_descent_complete,
        complete_factor_reconstruction_fibre_retained: chart
            .complete_factor_reconstruction_fibre_retained,
        exterior_occurrence_consulted: chart.exterior_occurrence_consulted,
        every_branch_current_nonzero,
        every_branch_identity_distinct,
    };
    if audit.factor_population == 0
        || audit.winding_population == 0
        || audit.rank == 0
        || audit.rank > audit.winding_population
        || audit.kernel_dimension + audit.rank != audit.factor_population
        || !audit.total_factor_coverage
        || !audit.orientation_covariant
        || !audit.receiver_history_fibres_singleton
        || !audit.q_descent_complete
        || !audit.complete_factor_reconstruction_fibre_retained
        || audit.exterior_occurrence_consulted
        || !audit.every_branch_current_nonzero
        || !audit.every_branch_identity_distinct
    {
        return Err("the UAR3-D0 constitutive chart failed its exact receiver gate".into());
    }
    fs::write(
        output.join("uar3-d0-factor-winding-chart.json"),
        serde_json::to_vec_pretty(&chart)?,
    )?;
    fs::write(
        output.join("uar3-d0-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", chart.identity_sha256);
    Ok(())
}

fn repository_root() -> Result<PathBuf, Box<dyn Error>> {
    let mut root = std::env::current_dir()?;
    while !root.join("Cargo.toml").is_file() || !root.join("docs/plans/THE_ROADMAP.md").is_file() {
        if !root.pop() {
            return Err("repository root was not found".into());
        }
    }
    Ok(root)
}
