//! Emit the validated linked-torus `FieldSessionSpec` consumed by Athena field drivers.

#[path = "support/linked_torus_field.rs"]
mod linked_torus_field;

use holonics_hna::native::{FieldSessionSpec, FieldSourceChart, FieldTextCodec, GeometricFieldSpec};
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
    if args.next().is_some() {
        return Err("usage: athena_geometric_spec [subdivisions] [refinement-steps] [relaxation-bits] [output.json]".into());
    }
    let geometry = linked_torus_field::linked_torus_field_spec(
        subdivisions,
        refinement_steps,
        relaxation_bits,
    )?;
    let slots = geometry.slot_junctions.len();
    let context_symbols = (slots / 4) * 2;
    let section_symbols = ((slots - context_symbols) / 2) * 2;
    let spec = FieldSessionSpec {
        symbols: (0..16).map(|n| format!("{n:x}")).collect(),
        section_symbols,
        context_symbols,
        region_offsets: Vec::new(),
        source_chart: FieldSourceChart::GeometricRegions,
        geometry: Some(geometry),
        codec: FieldTextCodec::Utf8Nibbles,
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
