use std::path::Path;

use athena_alpha::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperationOccurrence, NativeFullOperatorSession, NativeOperatorResidence,
        dismantle_full_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    prompt_token_population: usize,
    first_selected_token: u32,
    first_rendered_token: String,
    first_equal_maximum_population: usize,
    first_cycle_generation: u64,
    second_context_token_population: usize,
    second_selected_token: u32,
    second_rendered_token: String,
    second_equal_maximum_population: usize,
    second_cycle_generation: u64,
    operation_population_per_cycle: usize,
    both_cycles_complete: bool,
    second_cycle_consumed_first_successor: bool,
    predecessor_occurrence_rejected: bool,
    independently_rebuilt_generation_rejected: bool,
    application_opened_no_coefficient_container: bool,
    final_faces_are_native_vocabulary_faces: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let prompt = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "The receiver".to_owned());
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let prompt_tokens = application.encode(&prompt)?;
    if prompt_tokens.is_empty() {
        return Err("the application encoded no occurrence".into());
    }
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    let first = session.advance_cycle(&prompt_tokens)?;
    let first_face = application.render(&first.final_emission)?;
    let first_emission_width = first.final_emission.width;
    let first_generation = first.successor.generation();
    let predecessor_occurrence_rejected =
        !first
            .successor
            .accepts_occurrence(&NativeFullOperationOccurrence {
                ordinal: first_generation - 1,
                row_addresses: vec![first_face.selected],
                morphology_current: None,
            });
    let independently_rebuilt_generation_rejected =
        !first
            .successor
            .accepts_occurrence(&NativeFullOperationOccurrence {
                ordinal: 0,
                row_addresses: vec![first_face.selected],
                morphology_current: None,
            });
    let mut second_context = prompt_tokens.clone();
    second_context.push(first_face.selected);
    let first_successor_generation = first.successor.generation();
    let second = first.successor.advance_cycle(&second_context)?;
    let second_face = application.render(&second.final_emission)?;
    let vocabulary = 262_144usize;
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            prompt_token_population: prompt_tokens.len(),
            first_selected_token: first_face.selected,
            first_rendered_token: first_face.rendered,
            first_equal_maximum_population: first_face.equal_score_population.len(),
            first_cycle_generation: first_generation,
            second_context_token_population: second_context.len(),
            second_selected_token: second_face.selected,
            second_rendered_token: second_face.rendered,
            second_equal_maximum_population: second_face.equal_score_population.len(),
            second_cycle_generation: second.successor.generation(),
            operation_population_per_cycle: returned.native.operations.len(),
            both_cycles_complete: second.successor.cycle_complete(),
            second_cycle_consumed_first_successor: second
                .traces
                .first()
                .is_some_and(|trace| trace.predecessor_generation >= first_successor_generation)
                && second.successor.generation()
                    == first_successor_generation + returned.native.operations.len() as u64,
            predecessor_occurrence_rejected,
            independently_rebuilt_generation_rejected,
            application_opened_no_coefficient_container: true,
            final_faces_are_native_vocabulary_faces: first_emission_width == vocabulary
                && second.final_emission.width == vocabulary
                && first_face.score_population == vocabulary
                && second_face.score_population == vocabulary,
        })?
    );
    Ok(())
}
