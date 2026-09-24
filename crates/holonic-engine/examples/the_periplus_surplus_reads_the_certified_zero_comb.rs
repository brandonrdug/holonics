//! The periplus surplus over the certified zero comb.
//!
//! The September 14/15 record's width law at a hypothetical off-seam member is
//! `d' <= -1/d - J_R + epsilon_R` with the admitted population's surplus
//!
//! ```text
//! J_R(s) = 2 sum_{w != s, s*} m_w (Re(s) - Re(w)) / |s - w|^2  >= 0,
//! ```
//!
//! every summand nonnegative under the rightmost ordering. This driver reads one or more
//! certified eta-zero atlases (each lineage's final receiver is a certified box holding
//! exactly one zero, fixed on the critical line by the atlas's symmetry read), computes the
//! certified surplus and margin for every lineage at supplied dyadic widths, and reports the
//! macroscopic flux pattern: the certified band windings (the counting current), the dyadic
//! shell of every zero, the per-shell margin minima, the surplus coefficient
//! `C = d*J_R/d^2`, and the largest certified gap per shell.
//!
//! **Certificate direction.** The certified comb is the artifacts' own lineage population.
//! Every admitted zero outside the artifacts contributes a nonnegative term, so omitting it
//! keeps each margin a valid lower bound; no exterior estimate enters anywhere. The
//! displacement current `epsilon_R` is not measured here: it is the Lean face
//! (`FiniteZeroCurrent`, `FosterClassFlux.comb'_sub_le`, `FoldedSourceBounds`) that the
//! certified comb constant is to dominate. A float appears nowhere: all statistics are exact
//! rationals; every printed or stored display value is an outward-rounded enclosure with its
//! declared display bits.
//!
//! Usage:
//! `the_periplus_surplus_reads_the_certified_zero_comb [artifact ...] [widths] [output|-]`
//! Widths default to `1/2,1/4,1/16,1/256` (dyadic, comma separated).

use num_bigint::BigInt;
use num_traits::Zero;
use holonics::geometry::{Rat, RatInterval, read_atlas};
use serde_json::{Value, json};
use std::path::PathBuf;

type Result<T> = std::result::Result<T, String>;


const DEFAULT_ARTIFACTS: &[&str] = &[
    ".local/artifacts/hephaestus-zeta-information/atlas-12-36.ron",
    ".local/artifacts/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding/holonic-eta-ratio-atlas-resident-01024-01026.ron",
    ".local/artifacts/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding/holonic-eta-ratio-atlas-resident-04096-04098.ron",
    ".local/artifacts/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding/holonic-eta-ratio-atlas-resident-16384-16386.ron",
];

const DEFAULT_WIDTHS: &str = "1/2,1/4,1/16,1/256";

fn display(value: &Rat) -> Value {
    let shown = RatInterval::point(value.clone()).round_out(8);
    json!({"display": shown.lower.to_string(), "display_bits": 8})
}

fn display_interval(interval: &RatInterval) -> Value {
    let shown = interval.round_out(8);
    json!({"display": [shown.lower.to_string(), shown.upper.to_string()], "display_bits": 8})
}

/// The dyadic shell `2^k <= tau_lo < 2^(k+1)`, by exact integer comparison.
fn shell_of(tau_lo: &Rat) -> u32 {
    let mut k = 0u32;
    while tau_lo >= &Rat::from_integer(BigInt::from(1i64 << (k + 1))) {
        k += 1;
    }
    k
}

fn parse_rat(text: &str) -> Result<Rat> {
    let (numer, denom) = text.split_once('/').unwrap_or((text, "1"));
    let numer = BigInt::parse_bytes(numer.as_bytes(), 10).ok_or_else(|| format!("bad ratio {text}"))?;
    let denom = BigInt::parse_bytes(denom.as_bytes(), 10).ok_or_else(|| format!("bad ratio {text}"))?;
    if denom.is_zero() {
        return Err(format!("bad ratio {text}: zero denominator"));
    }
    Ok(Rat::new(numer, denom))
}

struct CertifiedMember {
    label: String,
    ordinal: usize,
    tau: RatInterval,
    root_winding: i32,
}

/// Certified distance interval between two certified tau boxes: [lo, hi], both ends exact.
fn distance_between(left: &RatInterval, right: &RatInterval) -> (Rat, Rat) {
    let lo = {
        let a = &right.lower - &left.upper;
        let b = &left.lower - &right.upper;
        if a > Rat::zero() {
            a
        } else if b > Rat::zero() {
            b
        } else {
            Rat::zero()
        }
    };
    let hi_a = &right.upper - &left.lower;
    let hi_b = &left.upper - &right.lower;
    let hi = if hi_a > hi_b { hi_a } else { hi_b };
    (lo, hi)
}

/// One lineage's certified surplus against the artifacts' certified population.
///
/// Every term is an exact rational: `2d/(d^2 + u_hi^2)` per certified neighbor (lower),
/// `2d/(d^2 + u_lo^2)` per neighbor (upper), plus the opposite member `d/(d^2 + gamma_up^2)`.
/// The margin is `d*J_R - 1`; the surplus coefficient is `C = d*J_R/d^2`.
fn surplus_certificate(member: &CertifiedMember, population: &[CertifiedMember], width: &Rat) -> Value {
    let d: &Rat = width;
    let d2 = d.clone() * d;
    let two_d = d + d;
    let mut lower_total = Rat::zero();
    let mut upper_total = Rat::zero();
    let mut contributors = 0usize;
    for other in population {
        if other.label == member.label && other.ordinal == member.ordinal {
            continue;
        }
        let (u_lo, u_hi) = distance_between(&member.tau, &other.tau);
        let factor_hi = d2.clone() + u_hi.clone() * u_hi;
        let factor_lo = d2.clone() + u_lo.clone() * u_lo;
        lower_total += &two_d / &factor_hi;
        upper_total += &two_d / &factor_lo;
        contributors += 1;
    }
    let opposite = d / &(d2.clone() + member.tau.upper.clone() * member.tau.upper.clone());
    lower_total += &opposite;
    upper_total += &opposite;

    let margin_lo = lower_total.clone() - Rat::from_integer(BigInt::from(1));
    let margin_hi = upper_total.clone() - Rat::from_integer(BigInt::from(1));
    let coefficient = lower_total.clone() / d2;
    json!({
        "label": member.label,
        "ordinal": member.ordinal,
        "shell": shell_of(&member.tau.lower),
        "tau_box": {
            "exact": [member.tau.lower.to_string(), member.tau.upper.to_string()],
            "display": display_interval(&member.tau),
        },
        "root_winding": member.root_winding,
        "certified_contributors": contributors,
        "width": d.to_string(),
        "dJ_R_lower": {"exact": lower_total.to_string(), "display": display(&lower_total)},
        "dJ_R_upper": {"exact": upper_total.to_string(), "display": display(&upper_total)},
        "M": {
            "exact": [margin_lo.to_string(), margin_hi.to_string()],
            "display": display_interval(&RatInterval::new(margin_lo, margin_hi)),
        },
        "C": {"exact": coefficient.to_string(), "display": display(&coefficient)},
    })
}

fn main() -> std::result::Result<(), String> {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let widths_argument = arguments.iter().find(|argument| argument.contains('/')).cloned();
    let artifacts: Vec<PathBuf> = arguments
        .iter()
        .filter(|argument| !argument.contains('/') || argument.ends_with(".ron"))
        .map(PathBuf::from)
        .collect();
    let artifacts = if artifacts.is_empty() {
        DEFAULT_ARTIFACTS.iter().map(PathBuf::from).collect()
    } else {
        artifacts
    };
    let widths: Vec<Rat> = match widths_argument {
        Some(text) => text
            .split(',')
            .map(parse_rat)
            .collect::<Result<Vec<_>>>(),
        None => DEFAULT_WIDTHS
            .split(',')
            .map(parse_rat)
            .collect::<Result<Vec<_>>>(),
    }?;

    let mut population: Vec<CertifiedMember> = Vec::new();
    let mut band_pattern = Vec::new();
    for path in &artifacts {
        let atlas = read_atlas(path).map_err(|error| format!("{}: {error}", path.display()))?;
        let label = path
            .file_name()
            .map(|name| name.to_string_lossy().to_string())
            .unwrap_or_default();
        for band in &atlas.bands {
            band_pattern.push(json!({
                "label": label,
                "band_tau": {"exact": [
                    band.winding.receiver.tau.lower.to_string(),
                    band.winding.receiver.tau.upper.to_string(),
                ]},
                "derived_start": band.config.euler_maclaurin_start,
                "winding": band.winding.winding,
                "crossings": band.winding.crossings.total(),
                "boundary_points": band.winding.polygon.len(),
            }));
        }
        for lineage in &atlas.zero_lineages {
            population.push(CertifiedMember {
                label: label.clone(),
                ordinal: population.len(),
                tau: lineage.final_receiver.tau.clone(),
                root_winding: lineage.root.winding,
            });
        }
    }
    if population.is_empty() {
        return Err("the certified artifacts carry no zero lineages".to_owned());
    }
    population.sort_by(|left, right| left.tau.lower.cmp(&right.tau.lower));
    for (ordinal, member) in population.iter_mut().enumerate() {
        member.ordinal = ordinal;
    }

    let mut per_shell: std::collections::BTreeMap<u32, Vec<usize>> = Default::default();
    for (index, member) in population.iter().enumerate() {
        per_shell.entry(shell_of(&member.tau.lower)).or_default().push(index);
    }

    let mut certificates = Vec::new();
    let mut shell_rows = Vec::new();
    for (shell, members) in &per_shell {
        // The largest certified successive gap inside the shell's certified population.
        let mut largest_gap: Option<(usize, usize, RatInterval)> = None;
        for window in members.windows(2) {
            let (a, b) = (&population[window[0]], &population[window[1]]);
            let gap = RatInterval::new(b.tau.lower.clone(), b.tau.upper.clone())
                .subtract(&RatInterval::new(a.tau.upper.clone(), a.tau.upper.clone()));
            let better = largest_gap
                .as_ref()
                .map(|(_, _, value)| gap.lower > value.lower)
                .unwrap_or(true);
            if better {
                largest_gap = Some((a.ordinal, b.ordinal, gap));
            }
        }
        let gap_row = largest_gap
            .map(|(from, to, value)| {
                json!({
                    "exact": [value.lower.to_string(), value.upper.to_string()],
                    "display": display_interval(&value),
                    "members": [from, to],
                })
            })
            .unwrap_or(Value::Null);
        let mut worst: Option<Value> = None;
        for index in members {
            let member = &population[*index];
            for width in &widths {
                let certificate = surplus_certificate(member, &population, width);
                let margin_lower = certificate["M"]["exact"][0]
                    .as_str()
                    .and_then(|text| parse_rat(text).ok())
                    .ok_or("unparsable margin receipt")?;
                let worse = worst
                    .as_ref()
                    .and_then(|row| row["M"]["exact"][0].as_str())
                    .and_then(|text| parse_rat(text).ok())
                    .map(|old| margin_lower < old)
                    .unwrap_or(true);
                if worse {
                    worst = Some(certificate.clone());
                }
                certificates.push(certificate);
            }
        }
        shell_rows.push(json!({
            "shell": shell,
            "height_span": {"exact": [
                population[members[0]].tau.lower.to_string(),
                population[*members.last().unwrap()].tau.upper.to_string(),
            ]},
            "certified_members": members.len(),
            "largest_gap": gap_row,
            "worst_margin_certificate": worst,
        }));
    }

    let receipts = json!({
        "provenance": {
            "date": "2026-09-15",
            "law": "periplus surplus d*J_R and margin M = d*J_R - 1 over the certified zero comb; every admitted term outside the artifacts is nonnegative and omitted, so each margin is a certified lower bound; epsilon_R is the Lean face (FiniteZeroCurrent, FosterClassFlux.comb'_sub_le, FoldedSourceBounds)",
            "arithmetic": "BigInt/BigRational only; distances are certified interval ends; outward rounding only for display at 8 bits",
            "artifacts": artifacts.iter().map(|path| path.display().to_string()).collect::<Vec<_>>(),
        },
        "certified_band_flux_pattern": band_pattern,
        "per_shell": shell_rows,
        "lineage_certificates": certificates,
    });
    let output = PathBuf::from(".local/artifacts/rh-periplus-census/periplus_surplus.json");
    if let Some(parent) = output.parent() {
        std::fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    std::fs::write(
        &output,
        serde_json::to_string_pretty(&receipts).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    println!(
        "certified members: {} across {} shells; receipts: {}",
        population.len(),
        per_shell.len(),
        output.display()
    );
    for row in &shell_rows {
        println!(
            "shell {} members {} largest_gap {} worst_M {}",
            row["shell"],
            row["certified_members"],
            row["largest_gap"]["display"],
            row["worst_margin_certificate"]["M"]["display"],
        );
    }
    Ok(())
}
