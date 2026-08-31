//! Generate a bounded eta-zero atlas from exact rational receiver currents, on the serial
//! apparatus. The law — bands, cut-reusing refinement, relations, verification — is
//! [`relational_geometry::eta_atlas`]; this driver only parses its arguments.
//!
//! No known zero ordinate is accepted as input. Integer height bands are scanned independently
//! at a start derived from the height, zero-bearing bands are refined through exact boundary
//! winding along the cut, and all reported coordinates remain rational intervals.
//!
//! Usage:
//! `holonic_eta_ratio_atlas <lower> <upper> [output|-] [workers] [grains] [grain_bits]`
//! `holonic_eta_ratio_atlas verify <artifact>`

use std::env;
use std::path::PathBuf;
use std::thread;

use relational_geometry::{
    HeadSource, SerialJets, atlas_base_config, atlas_summary, build_atlas, verify_artifact,
    write_atlas,
};

/// Returns land under `output/`, never at the repository root, one artifact per height range so
/// ranges scanned under the process aperture compose as files. The v1 artifact in the same
/// directory carries a declared start of twelve and is bound by content hash to its consumer; it
/// is not rewritten.
const ARTIFACT_DIRECTORY: &str = "output/holonic-eta-ratio-atlas";

fn default_artifact(lower: i64, upper: i64) -> PathBuf {
    PathBuf::from(format!(
        "{ARTIFACT_DIRECTORY}/holonic-eta-ratio-atlas-{lower:05}-{upper:05}.ron"
    ))
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if arguments.first().map(String::as_str) == Some("verify") {
        let path = arguments
            .get(1)
            .map(PathBuf::from)
            .ok_or_else(|| "verify needs the artifact path".to_owned())?;
        let report = verify_artifact(&path)?;
        print!("{report}");
        println!("artifact={}", path.display());
        return Ok(());
    }
    let parse = |index: usize, fallback: i64| -> Result<i64, String> {
        arguments
            .get(index)
            .map(|value| value.parse::<i64>().map_err(|error| error.to_string()))
            .transpose()
            .map(|value| value.unwrap_or(fallback))
    };
    let lower = parse(0, 12)?;
    let upper = parse(1, 36)?;
    let output = arguments
        .get(2)
        .filter(|value| value.as_str() != "-")
        .map(PathBuf::from)
        .unwrap_or_else(|| default_artifact(lower, upper));
    let available = thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1);
    let workers = parse(3, available.div_ceil(2) as i64)?.max(1) as usize;
    let grains = parse(4, 6)? as u32;
    let grain_bits = parse(5, 48)? as u32;

    let config = atlas_base_config();
    let atlas = build_atlas(
        lower,
        upper,
        workers,
        grains,
        grain_bits,
        14,
        &config,
        &SerialJets.apparatus(),
        &|| Ok(SerialJets),
    )?;
    write_atlas(&atlas, &output)?;
    print!("{}", atlas_summary(&atlas));
    println!("artifact={}", output.display());
    Ok(())
}
