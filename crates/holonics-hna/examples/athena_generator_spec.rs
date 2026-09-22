//! Emit a validated fixed-generator Athena session declaration.
//!
//! The JSON describes a source/receiver mathematical boundary and its native fixed topology. It
//! does not assert successful general conversation or a universal text model.

#[path = "support/generator_machine.rs"]
mod generator_machine;

use holonics_hna::native;
use std::{env, fs, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args().skip(1);
    let generators = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()?
        .unwrap_or(1);
    let source_aperture = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()?
        .unwrap_or(4);
    let response_aperture = args
        .next()
        .map(|value| value.parse::<usize>())
        .transpose()?
        .unwrap_or(4);
    let output = args.next().map(PathBuf::from);
    if args.next().is_some() {
        return Err("usage: athena_generator_spec [generators] [source-aperture] [response-aperture] [output.json]".into());
    }
    let spec =
        generator_machine::generator_session_spec(generators, source_aperture, response_aperture)?;
    let json = serde_json::to_string_pretty(&spec)?;
    if let Some(path) = output {
        fs::write(path, format!("{json}\n"))?;
    } else {
        println!("{json}");
    }
    Ok(())
}
