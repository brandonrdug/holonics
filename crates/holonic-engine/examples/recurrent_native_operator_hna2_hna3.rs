use std::path::PathBuf;

use holonic_engine::{
    embedding_fiber::ResidentReadout,
    foreign_map::manifest_safetensors,
    native_ecology::holonic_intelligence::{
        NativeOperatorOccurrence, ResidentOperatorMorphology, dismantle_native_operator,
        mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    schema: &'static str,
    device: String,
    carrier_extent: usize,
    interaction_extent: usize,
    resident_coefficient_octets: usize,
    first_generation: u64,
    second_generation: u64,
    chronology: Vec<u64>,
    passage_slots: usize,
    refusals: usize,
    first_emission_differs_from_second_source: bool,
    second_step_consumed_first_successor: bool,
    first_emission_population: usize,
    second_emission_population: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/home/b/models/gemma-4-E4B-it"));
    let returned = dismantle_native_operator(&root, 0)?;
    let container_path = root.join("model.safetensors");
    let (mut file, container) = manifest_safetensors(
        container_path
            .to_str()
            .ok_or("the container path is not text")?,
    )?;
    let embedding_name = "model.language_model.embed_tokens.weight";
    let per_layer_name = "model.language_model.embed_tokens_per_layer.weight";
    let (first_carrier, _) = container.read_rows_bf16(&mut file, embedding_name, 818, 1)?;
    let (second_carrier, _) = container.read_rows_bf16(&mut file, embedding_name, 18_740, 1)?;
    let (first_per_layer, per_layer_width) =
        container.read_rows_bf16(&mut file, per_layer_name, 818, 1)?;
    let (second_per_layer, _) =
        container.read_rows_bf16(&mut file, per_layer_name, 18_740, 1)?;
    if per_layer_width < returned.native.interaction_extent {
        return Err("the per-layer occurrence is narrower than the admitted interaction".into());
    }
    let first_interaction = first_per_layer[..returned.native.interaction_extent].to_vec();
    let second_interaction = second_per_layer[..returned.native.interaction_extent].to_vec();

    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let resident = ResidentOperatorMorphology::mount(&surface, &returned.native)?;
    let grain = resident.finest_initial_grain(&first_carrier)?;

    let mut session = resident.mount_initial(&first_carrier, grain)?;
    let mut first_emission = Vec::new();
    let mut first_trace = None;
    let mut joined = true;
    for ordinal in 0..6u64 {
        let interaction_words = if session.operation_at() == 2 {
            first_interaction.clone()
        } else {
            Vec::new()
        };
        let step = session.advance(NativeOperatorOccurrence {
            ordinal,
            interaction_words,
        })?;
        joined &= step.trace.predecessor_generation == ordinal;
        first_emission = step.emission.intervals.clone();
        first_trace = Some(step.trace.clone());
        session = step.successor;
    }
    let first_generation = session.generation();
    let first_trace = first_trace.ok_or("the first recurrence emitted no trace")?;
    let mut second_emission = Vec::new();
    for ordinal in 6..12u64 {
        let interaction_words = if session.operation_at() == 2 {
            second_interaction.clone()
        } else {
            Vec::new()
        };
        let step = session.advance(NativeOperatorOccurrence {
            ordinal,
            interaction_words,
        })?;
        joined &= step.trace.predecessor_generation == ordinal;
        second_emission = step.emission.intervals.clone();
        session = step.successor;
    }

    let mut comparison = resident.mount_initial(&second_carrier, grain)?;
    let mut comparison_emission = Vec::new();
    for ordinal in 0..6u64 {
        let interaction_words = if comparison.operation_at() == 2 {
            second_interaction.clone()
        } else {
            Vec::new()
        };
        let step = comparison.advance(NativeOperatorOccurrence {
            ordinal,
            interaction_words,
        })?;
        comparison_emission = step.emission.intervals.clone();
        comparison = step.successor;
    }
    let differs = first_emission != comparison_emission;
    if !differs || session.chronology() != (0..12u64).collect::<Vec<_>>() {
        return Err("the recurrent operation did not distinguish the actual occurrences".into());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            schema: "holonic-engine.hna2-hna3-recurrent-operator-receipt.v1",
            device: resident.device_name().to_owned(),
            carrier_extent: returned.native.carrier_extent,
            interaction_extent: returned.native.interaction_extent,
            resident_coefficient_octets: resident.resident_coefficient_octets(),
            first_generation,
            second_generation: session.generation(),
            chronology: session.chronology().to_vec(),
            passage_slots: first_trace.passage_slot_population,
            refusals: first_trace.refusal_population,
            first_emission_differs_from_second_source: differs,
            second_step_consumed_first_successor: joined && first_generation == 6,
            first_emission_population: first_emission.len(),
            second_emission_population: second_emission.len(),
        })?
    );
    Ok(())
}
