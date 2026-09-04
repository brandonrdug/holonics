use std::path::PathBuf;

use holonics_hna::AthenaTextOccurrenceApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        ResidentOperatorMorphology, dismantle_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct ApplicationReturn {
    application: &'static str,
    material: &'static str,
    entering_token: u32,
    emitted_token: u32,
    emitted_surface: String,
    equal_score_population: usize,
    collapsed_intervals: usize,
    generation: u64,
}

#[derive(Serialize)]
struct MatrixReceipt {
    schema: &'static str,
    device: String,
    native_morphology_operation_population: usize,
    application_population: usize,
    score_population_per_application: usize,
    hot_language_or_format_branches: usize,
    returns: Vec<ApplicationReturn>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/home/b/models/gemma-4-E4B-it"));
    let returned = dismantle_native_operator(&root, 0)?;
    let mut application = AthenaTextOccurrenceApplication::open(
        &root,
        0,
        returned.native.carrier_extent,
        returned.native.interaction_extent,
    )?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let resident = ResidentOperatorMorphology::mount(&surface, &returned.native)?;
    let vocabulary = application.mount_vocabulary(&readout)?;
    let mut returns = Vec::new();
    let mut score_population = None;
    for (kind, material) in [
        ("text", "Explain holonics briefly."),
        ("coding", "fn add(a: i32, b: i32) -> i32 {"),
        ("mathematics", "theorem add_zero (n : Nat) : n + 0 = n := by"),
    ] {
        let tokens = application.encode(material)?;
        let entering = *tokens.last().ok_or("one application encoded to nothing")?;
        let (carrier, interaction) = application.occurrence_carriers(entering)?;
        let grain = resident.finest_initial_grain(&carrier)?;
        let branch = resident
            .mount_initial(&carrier, grain)?
            .advance_branch(&interaction)?;
        let emission = branch
            .emissions
            .last()
            .ok_or("one application emitted no carrier")?;
        let rendered = application.render_token(&vocabulary, emission)?;
        if let Some(population) = score_population {
            if population != rendered.score_population {
                return Err("application receivers did not share one complete vocabulary".into());
            }
        } else {
            score_population = Some(rendered.score_population);
        }
        returns.push(ApplicationReturn {
            application: kind,
            material,
            entering_token: entering,
            emitted_token: rendered.selected,
            emitted_surface: rendered.rendered,
            equal_score_population: rendered.equal_score_population.len(),
            collapsed_intervals: rendered.collapsed_interval_population,
            generation: branch.successor.generation(),
        });
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&MatrixReceipt {
            schema: "athena-alpha.recurrent-application-matrix-hna5.v1",
            device: resident.device_name().to_owned(),
            native_morphology_operation_population: returned.native.operations.len(),
            application_population: returns.len(),
            score_population_per_application: score_population.unwrap_or(0),
            hot_language_or_format_branches: 0,
            returns,
        })?
    );
    Ok(())
}
