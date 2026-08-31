//! The eta-zero atlas with the head of every boundary jet formed on the card; the serial owner
//! as the control.
//!
//! A nontrivial zero of zeta is a winding: the image of a receiver box's boundary under `eta`
//! winds around the origin once per zero inside, and a box symmetric about the critical line
//! that holds exactly one zero holds it **on** the line, because reflection carries zeros to
//! zeros and fixes only that line (`RH.theZeroSetIsReflectionStable`,
//! `RH.theOffLineZeroIsNeverAlone`, kernel-checked). The law — bands at a start derived from the
//! height, breadth-first certification, refinement that certifies only the cut, verification —
//! is [`relational_geometry::eta_atlas`] and is shared with the serial driver. This driver plugs
//! in [`ResidentEtaHead`], which forms the `O(N)` head of every pending midpoint of one depth in
//! one launch of `kernels/exact_eta_head.cu` in exact fixed-point interval arithmetic.
//!
//! `control` runs, per band: the depth-first serial owner; the library's breadth-first walk with
//! serial jets (must reproduce the first receipt exactly — same law, same arithmetic); the
//! resident walk (must return the same winding); and, on a zero-bearing band, one cut-reusing
//! split against a fresh certification of the child (same winding), with times. Run with
//! `PATH=/opt/cuda/bin:$PATH`.
//!
//! Usage:
//! `... -- <lower> <upper> [output|-] [workers] [grains] [grain_bits]`
//! `... -- control <lower> <upper> [grain_bits]`
//! `... -- regrain <artifact> [grains] [workers]`
//! `... -- verify <artifact>`

use holonic_engine::ResidentEtaHead;
use num_bigint::BigInt;
use num_rational::BigRational;
use relational_geometry::{
    Field, HeadSource, RatInterval, SerialJets, atlas_base_config, atlas_summary, boundary_winding,
    build_atlas, derive_euler_maclaurin_start, eta_boundary_winding, read_atlas, receiver_band,
    regrain_atlas, split_winding, verify_artifact, verify_winding, write_atlas,
};
use std::env;
use std::fs;
use std::path::PathBuf;
use std::thread;
use std::time::Instant;

const ARTIFACT_DIRECTORY: &str =
    "output/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding";

fn default_artifact(lower: i64, upper: i64) -> PathBuf {
    PathBuf::from(format!(
        "{ARTIFACT_DIRECTORY}/holonic-eta-ratio-atlas-resident-{lower:05}-{upper:05}.ron"
    ))
}

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn mount() -> Result<ResidentEtaHead, String> {
    ResidentEtaHead::mount().map_err(|error| error.to_string())
}

fn control(lower: i64, upper: i64, grain_bits: u32) -> Result<(), String> {
    let base = atlas_base_config();
    let mut card = mount()?;
    let mut serial = SerialJets;
    let mut rows = Vec::new();
    for band in lower..upper {
        let receiver = receiver_band(RatInterval::new(integer(band), integer(band + 1)));
        let config = derive_euler_maclaurin_start(&receiver, &base, grain_bits)
            .map_err(|error| error.to_string())?;
        let started = Instant::now();
        let depth_first =
            eta_boundary_winding(&receiver, &config, 14).map_err(|e| e.to_string())?;
        let depth_first_seconds = started.elapsed().as_secs_f64();
        let started = Instant::now();
        let breadth_first = boundary_winding(&mut serial, Field::Eta, &receiver, &config, 14)?;
        let breadth_first_seconds = started.elapsed().as_secs_f64();
        if breadth_first != depth_first {
            return Err(format!(
                "band [{band},{}]: the breadth-first serial walk did not reproduce the depth-first receipt",
                band + 1
            ));
        }
        let device_before = card.device_seconds;
        let started = Instant::now();
        let resident = boundary_winding(&mut card, Field::Eta, &receiver, &config, 14)?;
        let resident_seconds = started.elapsed().as_secs_f64();
        let device_seconds = card.device_seconds - device_before;
        if resident.winding != depth_first.winding {
            return Err(format!(
                "band [{band},{}]: resident winding {} differs from serial {}",
                band + 1,
                resident.winding,
                depth_first.winding
            ));
        }
        verify_winding(&resident, &format!("resident band {band}"))?;
        let mut row = format!(
            "band tau=[{},{}] start={} winding={} | depth-first serial {:.3} s ({} points) | breadth-first serial {:.3} s (identical receipt) | resident {:.3} s ({} points, device {:.3} s, launches {})",
            band,
            band + 1,
            config.euler_maclaurin_start,
            depth_first.winding,
            depth_first_seconds,
            depth_first.polygon.len(),
            breadth_first_seconds,
            resident_seconds,
            resident.polygon.len(),
            device_seconds,
            card.launches
        );
        if depth_first.winding == 1 {
            let split = &receiver.tau.lower + BigRational::new(BigInt::from(1), BigInt::from(2));
            let started = Instant::now();
            let (left, right) =
                split_winding(&mut card, Field::Eta, &resident, &split, &config, 14)?;
            let split_seconds = started.elapsed().as_secs_f64();
            verify_winding(&left, &format!("split band {band} left"))?;
            verify_winding(&right, &format!("split band {band} right"))?;
            if left.winding + right.winding != 1 {
                return Err(format!(
                    "band [{band},{}]: split windings do not add to one",
                    band + 1
                ));
            }
            let child = if left.winding == 1 { &left } else { &right };
            let started = Instant::now();
            let fresh = boundary_winding(&mut card, Field::Eta, &child.receiver, &config, 14)?;
            let fresh_seconds = started.elapsed().as_secs_f64();
            if fresh.winding != child.winding {
                return Err(format!(
                    "band [{band},{}]: fresh child winding disagrees with the split",
                    band + 1
                ));
            }
            row.push_str(&format!(
                " | split at {split}: windings ({},{}); parent {} segments, children {} in {:.3} s; fresh child {:.3} s ({} points)",
                left.winding,
                right.winding,
                resident.segments.len(),
                left.segments.len() + right.segments.len(),
                split_seconds,
                fresh_seconds,
                fresh.polygon.len()
            ));
        }
        println!("{row}");
        rows.push(row);
    }
    fs::create_dir_all(ARTIFACT_DIRECTORY).map_err(|e| e.to_string())?;
    let path = format!("{ARTIFACT_DIRECTORY}/control-{lower:05}-{upper:05}.json");
    let receipt = format!(
        "{{\n  \"scan\": [{lower}, {upper}],\n  \"grain_bits\": {grain_bits},\n  \"launches\": {},\n  \"lanes\": {},\n  \"device_seconds\": {:.3},\n  \"rows\": [\n{}\n  ]\n}}\n",
        card.launches,
        card.lanes,
        card.device_seconds,
        rows.iter()
            .map(|r| format!("    \"{}\"", r.replace('"', "'")))
            .collect::<Vec<_>>()
            .join(",\n")
    );
    fs::write(&path, receipt).map_err(|e| e.to_string())?;
    println!("artifact={path}");
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
            let report = verify_artifact(&path)?;
            print!("{report}");
            println!("artifact={}", path.display());
            return Ok(());
        }
        Some("regrain") => {
            let path = arguments
                .get(1)
                .map(PathBuf::from)
                .ok_or_else(|| "regrain needs the artifact path".to_owned())?;
            let grains: u32 = arguments.get(2).and_then(|v| v.parse().ok()).unwrap_or(12);
            let available = thread::available_parallelism()
                .map(|count| count.get())
                .unwrap_or(1);
            let workers: usize = arguments
                .get(3)
                .and_then(|v| v.parse().ok())
                .unwrap_or(available);
            let mut atlas = read_atlas(&path)?;
            let before: Vec<String> = atlas
                .zero_lineages
                .iter()
                .map(|l| l.final_receiver.tau.to_string())
                .collect();
            let started = Instant::now();
            regrain_atlas(&mut atlas, grains, workers, &mount)?;
            write_atlas(&atlas, &path)?;
            println!(
                "regrained {} lineages to {grains} grains in {:.1} s",
                atlas.zero_lineages.len(),
                started.elapsed().as_secs_f64()
            );
            for (b, l) in before.iter().zip(atlas.zero_lineages.iter()).take(3) {
                println!("  {b} -> {}", l.final_receiver.tau);
            }
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
            return control(lower, upper, grain_bits);
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
    let grains = parse(4, 6)? as u32;
    let grain_bits = parse(5, 48)? as u32;
    let config = atlas_base_config();
    let apparatus = mount()?.apparatus();
    let atlas = build_atlas(
        lower, upper, workers, grains, grain_bits, 14, &config, &apparatus, &mount,
    )?;
    write_atlas(&atlas, &output)?;
    print!("{}", atlas_summary(&atlas));
    println!("artifact={}", output.display());
    Ok(())
}
