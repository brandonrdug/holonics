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
    advanced_operation_population: usize,
    successor_generation: u64,
    successor_operation_at: usize,
    chronology_is_exact_prefix: bool,
    resident_coefficient_octets: u64,
    next_primitive: NativeOperationPrimitive,
    last_emission_rows: usize,
    last_emission_width: usize,
    last_emission_nonempty: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let stop = returned
        .native
        .operations
        .iter()
        .rposition(|operation| matches!(operation.primitive, NativeOperationPrimitive::Contract))
        .ok_or("the complete graph has no tied boundary contraction")?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let mut session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    let mut last_rows = 0;
    let mut last_width = 0;
    let mut last_nonempty = false;
    for at in 0..stop {
        let addresses = if matches!(
            returned.native.operations[at].primitive,
            NativeOperationPrimitive::Lookup { .. }
        ) {
            vec![818, 18_740]
        } else {
            Vec::new()
        };
        let step = session
            .advance(NativeFullOperationOccurrence {
                ordinal: at as u64,
                row_addresses: addresses,
                morphology_current: None,
            })
            .map_err(|error| {
                format!(
                    "operation {at} {:?}: {error}",
                    returned.native.operations[at].primitive
                )
            })?;
        last_rows = step.emission.rows;
        last_width = step.emission.width;
        last_nonempty = !step.emission.intervals.is_empty();
        session = step.successor;
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            advanced_operation_population: stop,
            successor_generation: session.generation(),
            successor_operation_at: session.operation_at(),
            chronology_is_exact_prefix: session.chronology()
                == (0..stop as u64).collect::<Vec<_>>(),
            resident_coefficient_octets: returned.native.coefficient_octets()?,
            next_primitive: returned.native.operations[stop].primitive.clone(),
            last_emission_rows: last_rows,
            last_emission_width: last_width,
            last_emission_nonempty: last_nonempty,
        })?
    );
    Ok(())
}
