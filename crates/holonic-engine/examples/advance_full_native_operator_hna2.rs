use std::path::Path;

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
    predecessor_generation: u64,
    successor_generation: u64,
    successor_operation_at: usize,
    successor_chronology: Vec<u64>,
    successor_carrier_population: usize,
    occurrence_population: usize,
    emission_rows: usize,
    emission_width: usize,
    emission_grain: u32,
    point_interval_population: usize,
    distinct_occurrences_return_distinct_native_carriers: bool,
    constitutive_contraction_distinguishes_occurrences: bool,
    emission_is_the_successor_carrier_face: bool,
    trace_contains_no_source_name_or_path: bool,
    complete_resident_coefficient_octets: u64,
    operation_deed_launches: u64,
    operation_synchronizations: u64,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    let first = session.advance(NativeFullOperationOccurrence {
        ordinal: 0,
        row_addresses: vec![818, 18_740],
    })?;
    let distinct_occurrences_return_distinct_native_carriers = first.emission.intervals
        [..first.emission.width]
        != first.emission.intervals[first.emission.width..];
    let second = first.successor.advance(NativeFullOperationOccurrence {
        ordinal: 1,
        row_addresses: vec![818, 18_740],
    })?;
    let reshaped = second.successor.advance(NativeFullOperationOccurrence {
        ordinal: 2,
        row_addresses: Vec::new(),
    })?;
    let step = reshaped.successor.advance(NativeFullOperationOccurrence {
        ordinal: 3,
        row_addresses: Vec::new(),
    })?;
    let trace = serde_json::to_vec(&step.trace)?;
    let carries = |needle: &[u8]| trace.windows(needle.len()).any(|window| window == needle);
    let point_interval_population = step
        .emission
        .intervals
        .iter()
        .filter(|(lower, upper)| lower == upper)
        .count();
    let constitutive_contraction_distinguishes_occurrences = step.emission.intervals
        [..step.emission.width]
        != step.emission.intervals[step.emission.width..];
    let successor_face = step.successor.carrier_intervals(step.emission.carrier)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            predecessor_generation: step.trace.predecessor_generation,
            successor_generation: step.successor.generation(),
            successor_operation_at: step.successor.operation_at(),
            successor_chronology: step.successor.chronology().to_vec(),
            successor_carrier_population: step.successor.carrier_population(),
            occurrence_population: 2,
            emission_rows: step.emission.rows,
            emission_width: step.emission.width,
            emission_grain: step.emission.grain,
            point_interval_population,
            distinct_occurrences_return_distinct_native_carriers,
            constitutive_contraction_distinguishes_occurrences,
            emission_is_the_successor_carrier_face: successor_face == step.emission.intervals,
            trace_contains_no_source_name_or_path: ![
                b"model.".as_slice(),
                b"language".as_slice(),
                b".weight".as_slice(),
                root.as_bytes(),
            ]
            .iter()
            .any(|needle| carries(needle)),
            complete_resident_coefficient_octets: step.trace.resident_coefficient_octets,
            operation_deed_launches: step
                .trace
                .census_after
                .deed_launches
                .saturating_sub(step.trace.census_before.deed_launches),
            operation_synchronizations: step
                .trace
                .census_after
                .synchronizations
                .saturating_sub(step.trace.census_before.synchronizations),
        })?
    );
    Ok(())
}
