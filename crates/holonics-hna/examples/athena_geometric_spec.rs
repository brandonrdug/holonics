//! Emit the validated linked-torus `FieldSessionSpec` consumed by Athena field drivers.

#[path = "support/linked_torus_field.rs"]
mod linked_torus_field;

use holonics_hna::native::{
    FieldSessionSpec, FieldSourceChart, FieldTextCodec, GeometricFieldSpec, IncidentFieldOptions,
};
use std::{env, fs, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args().skip(1);
    let subdivisions = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()?
        .unwrap_or(1);
    let refinement_steps = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()?
        .unwrap_or(1);
    let relaxation_bits = args
        .next()
        .map(|value| value.parse::<u32>())
        .transpose()?
        .unwrap_or(1);
    let output = args.next().map(PathBuf::from);
    let mode = args.next().unwrap_or_else(|| "geometric".to_owned());
    if args.next().is_some() {
        return Err("usage: athena_geometric_spec [subdivisions] [refinement-steps] [relaxation-bits] [output.json] [geometric|incident|incident-quadrance]".into());
    }
    let mut geometry = linked_torus_field::linked_torus_field_spec(
        subdivisions,
        refinement_steps,
        relaxation_bits,
    )?;
    let slots = geometry.slot_junctions.len();
    let (source_chart, codec, symbols, section_symbols, context_symbols, incident) =
        if mode == "incident" || mode == "incident-quadrance" {
            let incident_slots =
                linked_torus_field::linked_torus_incident_slot_junctions(&geometry)?;
            geometry.slot_junctions = incident_slots;
            let owners = linked_torus_field::linked_torus_material_owners(&geometry)?;
            let response_aperture = (geometry.slot_junctions.len() / 4).max(1);
            (
                FieldSourceChart::IncidentField,
                FieldTextCodec::UnicodeScalars,
                vec!["a".into(), "b".into(), "c".into(), "d".into()],
                geometry.slot_junctions.len(),
                0,
                Some(IncidentFieldOptions {
                    participation: if mode == "incident-quadrance" {
                        holonics_hna::native::IncidentParticipationChart::QuadranceCurrent
                    } else {
                        Default::default()
                    },
                    local_roots: 1,
                    material_seed: 0x8a5c_19d3,
                    response_aperture,
                    response_port_start: None,
                    material_owners: owners,
                    solve_steps: 256,
                    solver: holonics_hna::native::IncidentFieldSolver::Richardson,
                }),
            )
        } else {
            let context_symbols = (slots / 4) * 2;
            let section_symbols = ((slots - context_symbols) / 2) * 2;
            (
                FieldSourceChart::GeometricRegions,
                FieldTextCodec::Utf8Nibbles,
                (0..16).map(|n| format!("{n:x}")).collect(),
                section_symbols,
                context_symbols,
                None,
            )
        };
    let spec = FieldSessionSpec {
        symbols,
        section_symbols,
        context_symbols,
        region_offsets: Vec::new(),
        source_chart,
        geometry: Some(geometry),
        incident,
        codec,
        fractional_bits: 48,
    };
    let json = serde_json::to_string_pretty(&spec)?;
    if let Some(path) = output {
        fs::write(path, format!("{json}\n"))?;
    } else {
        println!("{json}");
    }
    Ok(())
}
