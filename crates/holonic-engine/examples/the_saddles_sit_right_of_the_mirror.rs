//! The saddles between the zeros' basins, counted on each side of the mirror.
//!
//! `log|zeta|` is the magnitude potential of the flow whose vortices are the zeros. Its basins
//! tile the strip, one cone per zero, and two cones meet at a saddle of the potential — a zero
//! of the derivative of `zeta`. Speiser (1934): **the Riemann hypothesis holds if and only if
//! the derivative of `zeta` has no zero with `0 < sigma < 1/2`** — every saddle lies on the
//! right of the mirror. This driver counts them exactly, per integer height band, as windings
//! of the derivative around the two half boxes `[1/10, 1/2]` and `[1/2, 3]`, with the boundary
//! certified by the second derivative at every midpoint (the resident head supplies
//! `sum log^2 n · n^-s`) and a uniform Euler--Maclaurin bound on the third derivative. The
//! derivative has no zero with `sigma >= 3`, so the right box holds every saddle on the right; a
//! saddle with `sigma < 1/10` is outside the left box and is not claimed; a saddle **on** the
//! mirror would make the certification refuse by name rather than count it.
//!
//! `control` runs a band on the serial apparatus as well and requires the same windings.
//! Run with `PATH=/opt/cuda/bin:$PATH`.
//!
//! Usage:
//! `... -- <lower> <upper> [output|-] [workers] [grain_bits] [max_depth]`
//! `... -- control <lower> <upper>`
//! `... -- verify <artifact>`

use holonic_engine::ResidentEtaHead;
use num_bigint::BigInt;
use num_rational::BigRational;
use relational_geometry::{
    ComplexReceiverBox, Field, HeadSource, RatInterval, SerialJets, atlas_base_config,
    boundary_winding, build_saddle_atlas, derive_euler_maclaurin_start, saddle_summary,
    verify_saddle_artifact, verify_winding, write_saddle_atlas,
};
use std::env;
use std::path::PathBuf;
use std::thread;
use std::time::Instant;

const ARTIFACT_DIRECTORY: &str = ".local/artifacts/the_saddles_sit_right_of_the_mirror";

fn default_artifact(lower: i64, upper: i64) -> PathBuf {
    PathBuf::from(format!(
        "{ARTIFACT_DIRECTORY}/holonic-saddle-atlas-{lower:05}-{upper:05}.ron"
    ))
}

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn mount() -> Result<ResidentEtaHead, String> {
    ResidentEtaHead::mount().map_err(|error| error.to_string())
}

fn control(lower: i64, upper: i64, grain_bits: u32, max_depth: u32) -> Result<(), String> {
    let base = atlas_base_config();
    let mut card = mount()?;
    let mut serial = SerialJets;
    for band in lower..upper {
        let receiver = ComplexReceiverBox::new(
            RatInterval::new(rat(1, 10), rat(3, 1)),
            RatInterval::new(integer(band), integer(band + 1)),
        );
        let config = derive_euler_maclaurin_start(&receiver, &base, grain_bits)
            .map_err(|e| e.to_string())?;
        for (name, sigma) in [
            ("left", RatInterval::new(rat(1, 10), rat(1, 2))),
            ("right", RatInterval::new(rat(1, 2), rat(3, 1))),
        ] {
            let half =
                ComplexReceiverBox::new(sigma, RatInterval::new(integer(band), integer(band + 1)));
            let started = Instant::now();
            let resident =
                boundary_winding(&mut card, Field::ZetaPrime, &half, &config, max_depth)?;
            let resident_seconds = started.elapsed().as_secs_f64();
            verify_winding(&resident, &format!("resident {name} {band}"))?;
            let started = Instant::now();
            let serial_receipt =
                boundary_winding(&mut serial, Field::ZetaPrime, &half, &config, max_depth)?;
            let serial_seconds = started.elapsed().as_secs_f64();
            if serial_receipt.winding != resident.winding {
                return Err(format!(
                    "band [{band},{}] {name}: serial winding {} differs from resident {}",
                    band + 1,
                    serial_receipt.winding,
                    resident.winding
                ));
            }
            println!(
                "band tau=[{},{}] {name}: winding={} | resident {:.3} s ({} points) | serial {:.3} s ({} points)",
                band,
                band + 1,
                resident.winding,
                resident_seconds,
                resident.polygon.len(),
                serial_seconds,
                serial_receipt.polygon.len()
            );
        }
    }
    Ok(())
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    match arguments.first().map(String::as_str) {
        Some("verify") => {
            let path = arguments
                .get(1)
                .map(PathBuf::from)
                .ok_or_else(|| "verify needs the artifact path".to_owned())?;
            print!("{}", verify_saddle_artifact(&path)?);
            println!("artifact={}", path.display());
            return Ok(());
        }
        Some("control") => {
            let lower: i64 = arguments.get(1).and_then(|v| v.parse().ok()).unwrap_or(36);
            let upper: i64 = arguments
                .get(2)
                .and_then(|v| v.parse().ok())
                .unwrap_or(lower + 1);
            let grain_bits: u32 = arguments.get(3).and_then(|v| v.parse().ok()).unwrap_or(48);
            let max_depth: u32 = arguments.get(4).and_then(|v| v.parse().ok()).unwrap_or(16);
            return control(lower, upper, grain_bits, max_depth);
        }
        _ => {}
    }
    let parse = |index: usize, fallback: i64| -> Result<i64, String> {
        arguments
            .get(index)
            .map(|value| value.parse::<i64>().map_err(|error| error.to_string()))
            .transpose()
            .map(|value| value.unwrap_or(fallback))
    };
    let lower = parse(0, 36)?;
    let upper = parse(1, 40)?;
    let output = arguments
        .get(2)
        .filter(|value| value.as_str() != "-")
        .map(PathBuf::from)
        .unwrap_or_else(|| default_artifact(lower, upper));
    let available = thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1);
    let workers = parse(3, available.div_ceil(2) as i64)?.max(1) as usize;
    let grain_bits = parse(4, 48)? as u32;
    let max_depth = parse(5, 16)? as u32;
    let config = atlas_base_config();
    let apparatus = mount()?.apparatus();
    let atlas = build_saddle_atlas(
        lower, upper, workers, grain_bits, max_depth, &config, &apparatus, &mount,
    )?;
    write_saddle_atlas(&atlas, &output)?;
    print!("{}", saddle_summary(&atlas));
    println!("artifact={}", output.display());
    Ok(())
}
