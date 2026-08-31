use std::{env, error::Error, fs, path::PathBuf, time::Instant};

use life::athena_native::{
    transduce_source_neutral_exterior, SourceNeutralAthenaRest, SourceNeutralExteriorStep,
};
use num_traits::Zero;
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    "output/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0/",
    "athena-source-neutral.rest"
);
const CANDIDATE_MATERIAL: &str = concat!(
    "blueprint/",
    "THE_UNIFIED_ATHENA_BODY_RETURNS_TECHNICAL_CONDUCT_AND_BRANDON_THROUGH_COMPLETE_CULTIVATED_HISTORY.md"
);
const RETURNED_MATERIAL: &str = concat!(
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/",
    "HolonicMachineLearning.lean"
);
const OUTPUT: &str = concat!(
    "output/",
    "the_published_native_seam_returns_one_situated_difference_uar3"
);

#[derive(Serialize)]
struct Uar3D1Audit {
    truth_status: &'static str,
    parent_rest_identity_sha256: String,
    factor_winding_chart_identity_sha256: String,
    chart_rank: usize,
    chart_kernel_dimension: usize,
    published_emission_identity_sha256: String,
    exterior_return_identity_sha256: String,
    situated_difference_identity_sha256: String,
    factor_population: usize,
    nonzero_factor_difference_population: usize,
    returned_winding_rank: usize,
    returned_winding_nonzero_population: usize,
    selected_branch: usize,
    selected_factor: u32,
    complete_factor_reconstruction_fibre_retained: bool,
    exterior_source_fibre_reachable_from_productive_body: bool,
    returned_source_covector_equals_winding_difference: bool,
    chart_difference_equals_winding_difference: bool,
    candidate_file_chart_section: ExteriorFileChartSection,
    returned_file_chart_section: ExteriorFileChartSection,
}

#[derive(Clone, Serialize)]
struct ExteriorFileChartSection {
    path: &'static str,
    byte_start: usize,
    byte_end: usize,
}

fn main() -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let root = repository_root()?;
    let output = env::var_os("HOLONICS_OUTPUT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join(OUTPUT));
    fs::create_dir_all(&output)?;

    let bytes = fs::read(root.join(PREDECESSOR))?;
    eprintln!("uar3-d1 read-bytes {}ms", started.elapsed().as_millis());
    let rest = SourceNeutralAthenaRest::read(&bytes)?;
    drop(bytes);
    eprintln!("uar3-d1 read-rest {}ms", started.elapsed().as_millis());
    let parent_rest_identity_sha256 = rest.identity().to_owned();
    let resident = rest.mount_resident()?;
    eprintln!("uar3-d1 resident {}ms", started.elapsed().as_millis());
    // This chart is fully rested before either developmental source is mounted.
    let chart = resident.factor_winding_constitutive_chart()?;
    eprintln!("uar3-d1 chart {}ms", started.elapsed().as_millis());

    let candidate_material = fs::read(root.join(CANDIDATE_MATERIAL))?;
    let returned_material = fs::read(root.join(RETURNED_MATERIAL))?;
    let (candidate_section, candidate_file_chart_section) =
        first_file_chart_line(CANDIDATE_MATERIAL, &candidate_material)?;
    let (returned_section, returned_file_chart_section) =
        first_file_chart_line(RETURNED_MATERIAL, &returned_material)?;
    let (candidate_current, candidate_fibre) = transduce_source_neutral_exterior(
        resident.rest(),
        &format!(
            "uar3/developmental/candidate/{}:{}..{}",
            candidate_file_chart_section.path,
            candidate_file_chart_section.byte_start,
            candidate_file_chart_section.byte_end,
        ),
        candidate_section,
    )?;
    eprintln!(
        "uar3-d1 candidate-current {}ms",
        started.elapsed().as_millis()
    );
    let (returned_material_current, returned_fibre) = transduce_source_neutral_exterior(
        resident.rest(),
        &format!(
            "uar3/developmental/world-return/{}:{}..{}",
            returned_file_chart_section.path,
            returned_file_chart_section.byte_start,
            returned_file_chart_section.byte_end,
        ),
        returned_section,
    )?;
    eprintln!(
        "uar3-d1 returned-current {}ms",
        started.elapsed().as_millis()
    );
    drop(candidate_material);
    drop(returned_material);
    drop(candidate_fibre);
    drop(returned_fibre);

    let circulation = resident.begin_native_exterior(candidate_current)?;
    eprintln!("uar3-d1 circulation {}ms", started.elapsed().as_millis());
    let pending = match circulation.emit_next()? {
        SourceNeutralExteriorStep::Emission(pending) => pending,
        SourceNeutralExteriorStep::Terminal(_) => {
            return Err("the developmental candidate returned no published exterior seam".into());
        }
    };
    eprintln!("uar3-d1 emission {}ms", started.elapsed().as_millis());
    let published_emission_identity_sha256 = pending.emission().identity_sha256.clone();
    let returned_port = returned_material_current
        .crossed_structural_ports
        .iter()
        .find(|port| *port != &pending.emission().port)
        .cloned()
        .ok_or("the independent world occurrence returned no separating exterior port")?;
    drop(returned_material_current);
    let returned = pending.return_cultivation_occurrence(
        chart.clone(),
        "uar3/developmental/world-return/crossing",
        returned_port,
    )?;
    eprintln!(
        "uar3-d1 situated-difference {}ms",
        started.elapsed().as_millis()
    );
    let receipt = returned.receipt();
    let returned_source_covector_equals_winding_difference = receipt
        .situated_difference
        .causal_adjoint
        .returned_source_covector
        == receipt.winding_difference.returned_winding_covector;
    let chart_difference_equals_winding_difference =
        receipt.situated_difference.chart.oriented_difference
            == receipt.winding_difference.returned_winding_covector;
    let audit = Uar3D1Audit {
        truth_status: "implemented-exact; measured",
        parent_rest_identity_sha256,
        factor_winding_chart_identity_sha256: chart.identity_sha256.clone(),
        chart_rank: chart.rank,
        chart_kernel_dimension: chart.kernel_dimension,
        published_emission_identity_sha256,
        exterior_return_identity_sha256: receipt
            .exterior_return
            .returned_current_descent
            .identity_sha256
            .clone(),
        situated_difference_identity_sha256: receipt.situated_difference.identity_sha256.clone(),
        factor_population: receipt.winding_difference.factor_difference.len(),
        nonzero_factor_difference_population: receipt
            .winding_difference
            .factor_difference
            .iter()
            .filter(|coefficient| !coefficient.is_zero())
            .count(),
        returned_winding_rank: receipt.winding_difference.returned_winding_covector.len(),
        returned_winding_nonzero_population: receipt
            .winding_difference
            .returned_winding_covector
            .iter()
            .filter(|coefficient| !coefficient.is_zero())
            .count(),
        selected_branch: receipt.selected_branch,
        selected_factor: receipt.selected_factor,
        complete_factor_reconstruction_fibre_retained: receipt
            .complete_factor_reconstruction_fibre_retained,
        exterior_source_fibre_reachable_from_productive_body: receipt
            .exterior_source_fibre_reachable_from_productive_body,
        returned_source_covector_equals_winding_difference,
        chart_difference_equals_winding_difference,
        candidate_file_chart_section,
        returned_file_chart_section,
    };
    if audit.factor_population != chart.factor_native_addresses.len()
        || audit.nonzero_factor_difference_population == 0
        || audit.returned_winding_rank != chart.branch_functionals.len()
        || audit.returned_winding_nonzero_population == 0
        || !audit.complete_factor_reconstruction_fibre_retained
        || audit.exterior_source_fibre_reachable_from_productive_body
        || !audit.returned_source_covector_equals_winding_difference
        || !audit.chart_difference_equals_winding_difference
    {
        return Err("the UAR3-D1 world-return difference failed its exact gate".into());
    }
    fs::write(
        output.join("uar3-d1-situated-difference.json"),
        serde_json::to_vec_pretty(receipt)?,
    )?;
    eprintln!("uar3-d1 artifacts {}ms", started.elapsed().as_millis());
    fs::write(
        output.join("uar3-d1-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", audit.situated_difference_identity_sha256);
    Ok(())
}

fn first_file_chart_line<'a>(
    path: &'static str,
    bytes: &'a [u8],
) -> Result<(&'a [u8], ExteriorFileChartSection), Box<dyn Error>> {
    let byte_end = bytes
        .iter()
        .position(|octet| *octet == b'\n')
        .map(|at| at + 1)
        .unwrap_or(bytes.len());
    if byte_end == 0 {
        return Err(format!("the exterior file chart {path} has no first section").into());
    }
    Ok((
        &bytes[..byte_end],
        ExteriorFileChartSection {
            path,
            byte_start: 0,
            byte_end,
        },
    ))
}

fn repository_root() -> Result<PathBuf, Box<dyn Error>> {
    let mut root = std::env::current_dir()?;
    while !root.join("Cargo.toml").is_file() || !root.join("blueprint/THE_ROADMAP.md").is_file() {
        if !root.pop() {
            return Err("repository root was not found".into());
        }
    }
    Ok(root)
}
