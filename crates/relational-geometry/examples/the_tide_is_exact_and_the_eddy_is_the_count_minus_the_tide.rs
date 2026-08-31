//! The tide is exact, and the eddy is the count minus the tide.
//!
//! On the critical line `zeta(1/2 + it) = e^(-i theta(t)) Z(t)` with `Z` real, so the phase
//! current along the line is the Riemann--Siegel tide `theta(t)` plus a half-turn at every zero,
//! and the zero count is
//!
//! ```text
//!     N(T) = theta(T)/pi + 1 + S(T),      S(T) = (1/pi) arg zeta(1/2 + iT)
//! ```
//!
//! The atlas has `N(T)` at every integer height it scanned, as certified windings. This driver
//! reads those artifacts, forms `theta(T)` as an exact enclosure (Stirling's series with a shift
//! of sixteen, Machin's `pi`, Euler's arctangent series; `relational_geometry::riemann_siegel_theta`),
//! and returns the eddy `S(T)` as an exact rational interval at each integer height, together with
//! the Gram count of every band — the number of times the tide completes a half turn in it — set
//! against the band's winding. That comparison is Gram's law read as two families of marks taking
//! turns; the bands where they do not are the eddies visible without any float.
//!
//! Usage: `... -- [artifact directory] [output directory]`

use std::env;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use relational_geometry::{EtaRatioAtlas, RatInterval, pi_interval, riemann_siegel_theta};

const DEFAULT_ARTIFACTS: &str =
    "output/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding";
const DEFAULT_OUTPUT: &str = "output/the_tide_is_exact_and_the_eddy_is_the_count_minus_the_tide";

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

/// The integer part of an exact interval, when the interval does not straddle an integer.
fn floor_of(interval: &RatInterval) -> Option<BigInt> {
    let lower = interval.lower.floor().to_integer();
    let upper = interval.upper.floor().to_integer();
    if lower == upper { Some(lower) } else { None }
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let directory = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| DEFAULT_ARTIFACTS.to_owned()),
    );
    let output = PathBuf::from(
        arguments
            .get(1)
            .cloned()
            .unwrap_or_else(|| DEFAULT_OUTPUT.to_owned()),
    );

    // every verified band, in height order, from every artifact in the directory
    let mut paths: Vec<PathBuf> = fs::read_dir(&directory)
        .map_err(|error| error.to_string())?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| {
            path.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
                n.starts_with("holonic-eta-ratio-atlas-resident-") && n.ends_with(".ron")
            })
        })
        .collect();
    paths.sort();
    let mut bands: Vec<(i64, i32, u32)> = Vec::new(); // (tau_lower, winding, derived start)
    let mut config = None;
    for path in &paths {
        let encoded = fs::read_to_string(path).map_err(|error| error.to_string())?;
        let atlas: EtaRatioAtlas =
            ron::from_str(&encoded).map_err(|error| format!("{}: {error}", path.display()))?;
        if config.is_none() {
            config = Some(atlas.config.clone());
        }
        for band in &atlas.bands {
            let lower = band.winding.receiver.tau.lower.to_integer();
            let lower: i64 = lower
                .try_into()
                .map_err(|_| "band height beyond i64".to_owned())?;
            bands.push((
                lower,
                band.winding.winding,
                band.config.euler_maclaurin_start,
            ));
        }
    }
    let config = config.ok_or_else(|| "no artifacts found".to_owned())?;
    bands.sort_by_key(|band| band.0);
    bands.dedup_by_key(|band| band.0);
    for pair in bands.windows(2) {
        if pair[1].0 != pair[0].0 + 1 {
            return Err(format!(
                "the scanned bands are not contiguous at height {}",
                pair[0].0 + 1
            ));
        }
    }
    let first = bands
        .first()
        .map(|b| b.0)
        .ok_or_else(|| "no bands".to_owned())?;
    let last = bands.last().map(|b| b.0 + 1).unwrap_or(first);
    // no zero lies below the first scanned height; the first zero is above 14 and the scan begins at 12
    if first > 14 {
        return Err(format!(
            "the scan begins at {first}, above the first zero; N(T) cannot be formed"
        ));
    }

    let started = Instant::now();
    let pi = pi_interval(config.dyadic_bits);
    let mut rows: Vec<String> = Vec::new();
    let mut cumulative: i64 = 0;
    let mut theta_at: Vec<(i64, RatInterval)> = Vec::new();
    for height in first..=last {
        let theta =
            riemann_siegel_theta(&integer(height), &config).map_err(|error| error.to_string())?;
        theta_at.push((height, theta));
    }
    let mut max_eddy = BigRational::zero();
    let mut agree = 0usize;
    let mut disagree: Vec<(i64, i32, BigInt)> = Vec::new();
    let mut gram_open = 0usize;
    for (index, (height, winding, start)) in bands.iter().enumerate() {
        // N(height) after this band's lower edge: zeros with ordinate <= height are the bands below
        let n_lower = cumulative;
        cumulative += i64::from(*winding);
        let theta_lower = &theta_at[index].1;
        let theta_upper = &theta_at[index + 1].1;
        let tide_lower = theta_lower.divide(&pi).map_err(|e| e.to_string())?;
        let tide_upper = theta_upper.divide(&pi).map_err(|e| e.to_string())?;
        let eddy_upper = RatInterval::point(integer(cumulative - 1)).subtract(&tide_upper);
        let eddy_lower = RatInterval::point(integer(n_lower - 1)).subtract(&tide_lower);
        let gram = match (floor_of(&tide_upper), floor_of(&tide_lower)) {
            (Some(a), Some(b)) => Some(a - b),
            _ => None,
        };
        let magnitude = if eddy_upper.lower.abs() > eddy_upper.upper.abs() {
            eddy_upper.lower.abs()
        } else {
            eddy_upper.upper.abs()
        };
        if magnitude > max_eddy {
            max_eddy = magnitude;
        }
        match &gram {
            Some(g) if *g == BigInt::from(*winding) => agree += 1,
            Some(g) => disagree.push((*height, *winding, g.clone())),
            None => gram_open += 1,
        }
        rows.push(format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            height,
            height + 1,
            start,
            winding,
            cumulative,
            theta_upper.round_out(40),
            eddy_upper.round_out(40),
            gram.map(|g| g.to_string())
                .unwrap_or_else(|| "open".to_owned())
        ));
        let _ = eddy_lower;
    }
    let elapsed = started.elapsed().as_secs_f64();
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    let mut table = String::from(
        "tau_lower\ttau_upper\tderived_start\twinding\tN_at_tau_upper\ttheta_at_tau_upper_dyadic40\tS_at_tau_upper_dyadic40\tgram_points_in_band\n",
    );
    for row in &rows {
        table.push_str(row);
        table.push('\n');
    }
    fs::write(output.join("tide.tsv"), table).map_err(|error| error.to_string())?;
    let receipt = format!(
        "{{\n  \"scan\": [{first}, {last}],\n  \"bands\": {},\n  \"closures\": {},\n  \"theta_evaluations\": {},\n  \"elapsed_seconds\": {:.1},\n  \"max_abs_eddy_upper_bound\": \"{}\",\n  \"bands_where_winding_equals_gram_count\": {},\n  \"bands_where_they_differ\": {},\n  \"bands_with_open_gram_count\": {},\n  \"differences\": [{}]\n}}\n",
        bands.len(),
        cumulative,
        theta_at.len(),
        elapsed,
        max_eddy,
        agree,
        disagree.len(),
        gram_open,
        disagree
            .iter()
            .map(|(h, w, g)| format!(
                "{{\"tau_lower\": {h}, \"winding\": {w}, \"gram_points\": {g}}}"
            ))
            .collect::<Vec<_>>()
            .join(", ")
    );
    fs::write(output.join("receipt.json"), &receipt).map_err(|error| error.to_string())?;
    println!(
        "tide: bands={} closures={} theta_evaluations={} elapsed={:.1}s max|S| upper bound={} agree={} differ={} open={}",
        bands.len(),
        cumulative,
        theta_at.len(),
        elapsed,
        max_eddy,
        agree,
        disagree.len(),
        gram_open
    );
    for (h, w, g) in disagree.iter().take(40) {
        println!("  band [{h},{}]: winding {w}, gram points {g}", h + 1);
    }
    println!("artifact={}", output.join("tide.tsv").display());
    Ok(())
}
