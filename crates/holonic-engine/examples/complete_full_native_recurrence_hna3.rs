use std::path::Path;

use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperationOccurrence, NativeFullOperatorSession, NativeOperationPrimitive,
        NativeOperatorResidence, dismantle_full_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    graph_operation_population: usize,
    terminal_operation_population: usize,
    first_cycle_generation: u64,
    first_cycle_chronology_population: usize,
    first_cycle_complete: bool,
    first_cycle_successor_operation_at: usize,
    final_emission_rows: usize,
    final_emission_width: usize,
    final_emission_nonempty: bool,
    final_emission_equals_successor_carrier: bool,
    terminal_trace_joins_exactly: bool,
    second_cycle_first_operation: u32,
    second_cycle_generation: u64,
    second_cycle_used_returned_successor: bool,
    complete_resident_coefficient_octets: u64,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let graph_operations = returned.native.operations.len();
    let terminal_start = graph_operations.checked_sub(5).ok_or("short graph")?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let mut session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    for at in 0..terminal_start {
        let row_addresses = if matches!(
            returned.native.operations[at].primitive,
            NativeOperationPrimitive::Lookup { .. }
        ) {
            vec![818]
        } else {
            Vec::new()
        };
        session = session
            .advance(NativeFullOperationOccurrence {
                ordinal: at as u64,
                row_addresses,
            })?
            .successor;
    }
    let terminal = session.advance_terminal(NativeFullOperationOccurrence {
        ordinal: terminal_start as u64,
        row_addresses: Vec::new(),
    })?;
    let final_emission = terminal.emissions.last().ok_or("no final emission")?;
    let successor_face = terminal
        .successor
        .carrier_intervals(final_emission.carrier)?;
    let terminal_trace_joins_exactly = terminal
        .traces
        .windows(2)
        .all(|pair| pair[0].successor_generation == pair[1].predecessor_generation)
        && terminal
            .traces
            .first()
            .is_some_and(|trace| trace.predecessor_generation == terminal_start as u64)
        && terminal
            .traces
            .last()
            .is_some_and(|trace| trace.successor_generation == graph_operations as u64);
    let first_cycle_generation = terminal.successor.generation();
    let first_cycle_chronology_population = terminal.successor.chronology().len();
    let first_cycle_complete = terminal.successor.cycle_complete();
    let first_cycle_successor_operation_at = terminal.successor.operation_at();
    let final_emission_rows = final_emission.rows;
    let final_emission_width = final_emission.width;
    let final_emission_nonempty = !final_emission.intervals.is_empty();
    let final_emission_equals_successor_carrier = successor_face == final_emission.intervals;
    let second = terminal.successor.advance(NativeFullOperationOccurrence {
        ordinal: first_cycle_generation,
        row_addresses: vec![18_740],
    })?;
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            graph_operation_population: graph_operations,
            terminal_operation_population: terminal.traces.len(),
            first_cycle_generation,
            first_cycle_chronology_population,
            first_cycle_complete,
            first_cycle_successor_operation_at,
            final_emission_rows,
            final_emission_width,
            final_emission_nonempty,
            final_emission_equals_successor_carrier,
            terminal_trace_joins_exactly,
            second_cycle_first_operation: second.trace.operation.ordinal,
            second_cycle_generation: second.successor.generation(),
            second_cycle_used_returned_successor: second.trace.predecessor_generation
                == first_cycle_generation
                && second.trace.successor_generation == first_cycle_generation + 1,
            complete_resident_coefficient_octets: second.trace.resident_coefficient_octets,
        })?
    );
    Ok(())
}
