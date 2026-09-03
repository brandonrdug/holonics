use std::path::PathBuf;

use holonic_engine::native_ecology::holonic_intelligence::dismantle_native_operator;
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    schema: &'static str,
    carrier_extent: usize,
    interaction_extent: usize,
    operation_population: usize,
    coefficient_population: usize,
    norm_population: usize,
    hot_octets: usize,
    cold_tensor_population: usize,
    source_names_absent_from_hot: bool,
    first_basis_image_population: usize,
    omitted_source_operation_count: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/home/b/models/gemma-4-E4B-it"));
    let returned = dismantle_native_operator(&root, 0)?;
    returned.native.validate()?;
    let hot = serde_json::to_vec(&returned.native)?;
    let source_names_absent_from_hot = [
        returned.exterior.input_matrix.as_bytes(),
        returned.exterior.output_matrix.as_bytes(),
        returned.exterior.norm_gain.as_bytes(),
        returned.exterior.source_container.as_bytes(),
    ]
    .iter()
    .all(|name| !hot.windows(name.len()).any(|window| window == *name));
    if !source_names_absent_from_hot {
        return Err("source coordinates entered the hot morphology".into());
    }
    let first_basis_image = returned.native.matrices[0]
        .coefficients
        .chunks_exact(returned.native.carrier_extent)
        .map(|row| row[0].value())
        .collect::<Vec<_>>();
    if first_basis_image.len() != returned.native.interaction_extent {
        return Err("the first basis carrier did not cross the complete input cross-section".into());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            schema: "holonic-engine.hna1-operator-dismantling-receipt.v1",
            carrier_extent: returned.native.carrier_extent,
            interaction_extent: returned.native.interaction_extent,
            operation_population: returned.native.operations.len(),
            coefficient_population: returned
                .native
                .matrices
                .iter()
                .map(|matrix| matrix.coefficients.len())
                .sum(),
            norm_population: returned.native.norm_gain.len(),
            hot_octets: hot.len(),
            cold_tensor_population: 3,
            source_names_absent_from_hot,
            first_basis_image_population: first_basis_image.len(),
            omitted_source_operation_count: returned.insufficiency.omitted_source_operation_count,
        })?
    );
    Ok(())
}
