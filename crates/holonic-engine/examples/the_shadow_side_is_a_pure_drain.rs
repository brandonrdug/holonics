//! The shadow side of the mirror is a pure drain: `Re(ζ'/ζ) < 0` for `0 < σ < 1/2`, certified.
//!
//! `Re(ζ'/ζ)(s) = ∂_σ log|ζ(s)|`. A negative value everywhere left of the line says the magnitude
//! potential rises monotonically toward the mirror on the shadow side — the flow there only
//! leaves, it never eddies, and no saddle can sit where there is no stagnation to hold it. Under
//! RH this is Levinson–Montgomery's theorem, and it is the mechanism behind Speiser's; here it is
//! measured. Each point's `ζ` and `ζ'` are exact enclosures (the resident head, the serial tail),
//! `Re(ζ' ζ̄)/|ζ|²` is an interval, and a point is certified when that interval's upper end is
//! negative. Points whose interval straddles zero are reported as open, never counted.
//!
//! Usage: `... -- <lower> <upper> [sigmas as n/d, comma separated] [batch]`
//! Run with `PATH=/opt/cuda/bin:$PATH`.

use holonic_engine::ResidentEtaHead;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive};
use relational_geometry::{
    ComplexReceiverBox, HeadSource, RatInterval, atlas_base_config, derive_euler_maclaurin_start,
    zeta_evaluate_jet2_with_head,
};
use std::env;
use std::fs;
use std::time::Instant;

const OUTPUT: &str = ".local/artifacts/the_shadow_side_is_a_pure_drain";

fn parse_rational(text: &str) -> Option<BigRational> {
    let mut parts = text.split('/');
    let n: i64 = parts.next()?.trim().parse().ok()?;
    let d: i64 = parts
        .next()
        .map(|d| d.trim().parse().ok())
        .unwrap_or(Some(1))?;
    Some(BigRational::new(BigInt::from(n), BigInt::from(d)))
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let lower: i64 = arguments.first().and_then(|v| v.parse().ok()).unwrap_or(12);
    let upper: i64 = arguments.get(1).and_then(|v| v.parse().ok()).unwrap_or(100);
    let sigmas: Vec<BigRational> = arguments
        .get(2)
        .map(|s| s.split(',').filter_map(parse_rational).collect())
        .unwrap_or_else(|| {
            vec![
                parse_rational("1/10").unwrap(),
                parse_rational("1/4").unwrap(),
                parse_rational("2/5").unwrap(),
            ]
        });
    let batch: usize = arguments.get(3).and_then(|v| v.parse().ok()).unwrap_or(300);
    let base = atlas_base_config();
    let mut card = ResidentEtaHead::mount().map_err(|e| e.to_string())?;

    let mut points: Vec<(BigRational, i64)> = Vec::new();
    for t in lower..=upper {
        for sigma in &sigmas {
            points.push((sigma.clone(), t));
        }
    }
    let sigma_lower = sigmas.iter().min().cloned().unwrap();
    let sigma_upper = sigmas.iter().max().cloned().unwrap();
    let started = Instant::now();
    let mut certified_negative = 0usize;
    let mut certified_positive = 0usize;
    let mut open = 0usize;
    let mut rows: Vec<String> = Vec::new();
    let mut extremes: Vec<(String, f64, f64)> = Vec::new();
    for chunk in points.chunks(batch) {
        let t_hi = chunk.iter().map(|p| p.1).max().unwrap();
        let t_lo = chunk.iter().map(|p| p.1).min().unwrap();
        let whole = ComplexReceiverBox::new(
            RatInterval::new(sigma_lower.clone(), sigma_upper.clone()),
            RatInterval::new(
                BigRational::from_integer(BigInt::from(t_lo)),
                BigRational::from_integer(BigInt::from(t_hi)),
            ),
        );
        let config = derive_euler_maclaurin_start(&whole, &base, 48).map_err(|e| e.to_string())?;
        let receivers: Vec<ComplexReceiverBox> = chunk
            .iter()
            .map(|(sigma, t)| {
                ComplexReceiverBox::point(
                    sigma.clone(),
                    BigRational::from_integer(BigInt::from(*t)),
                )
            })
            .collect();
        let heads = card
            .heads(&receivers, &config)?
            .ok_or_else(|| "no heads".to_owned())?;
        for ((sigma, t), (receiver, head)) in chunk.iter().zip(receivers.iter().zip(heads.iter())) {
            let jet = zeta_evaluate_jet2_with_head(receiver, &config, Some(head))
                .map_err(|e| e.to_string())?;
            let zeta = &jet.jet.value;
            let prime = &jet.jet.first;
            // Re(ζ' ζ̄) / |ζ|²
            let numerator = prime
                .re
                .multiply(&zeta.re)
                .add(&prime.im.multiply(&zeta.im));
            let modulus_square = zeta.re.multiply(&zeta.re).add(&zeta.im.multiply(&zeta.im));
            let value = match numerator.divide(&modulus_square) {
                Ok(v) => v,
                Err(_) => {
                    open += 1;
                    rows.push(format!("{sigma}\t{t}\topen(|ζ| enclosure meets 0)"));
                    continue;
                }
            };
            let verdict = if value.upper.is_negative() {
                certified_negative += 1;
                "negative"
            } else if value.lower.is_positive() {
                certified_positive += 1;
                "POSITIVE"
            } else {
                open += 1;
                "open"
            };
            let lo = value.lower.to_f64().unwrap_or(f64::NAN);
            let hi = value.upper.to_f64().unwrap_or(f64::NAN);
            extremes.push((format!("{sigma}\t{t}"), lo, hi));
            rows.push(format!(
                "{sigma}\t{t}\t{verdict}\t{}\t{}",
                value.lower, value.upper
            ));
        }
    }
    let elapsed = started.elapsed().as_secs_f64();
    let least_negative = extremes
        .iter()
        .map(|e| e.2)
        .fold(f64::NEG_INFINITY, f64::max);
    let most_negative = extremes.iter().map(|e| e.1).fold(f64::INFINITY, f64::min);
    let summary = format!(
        "shadow drain: heights [{lower},{upper}] sigmas {:?} points={} certified_negative={certified_negative} certified_positive={certified_positive} open={open} elapsed_s={elapsed:.1} device_s={:.3} | Re(ζ'/ζ) ranged over [{most_negative:.4}, {least_negative:.4}]",
        sigmas.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        points.len(),
        card.device_seconds
    );
    println!("{summary}");
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;
    let path = format!("{OUTPUT}/drain-{lower:05}-{upper:05}.tsv");
    let mut table = String::from("sigma\tt\tverdict\tRe_zeta_prime_over_zeta_lower\tupper\n");
    for row in &rows {
        table.push_str(row);
        table.push('\n');
    }
    fs::write(&path, table).map_err(|e| e.to_string())?;
    fs::write(
        format!("{OUTPUT}/summary-{lower:05}-{upper:05}.txt"),
        summary,
    )
    .map_err(|e| e.to_string())?;
    println!("artifact={path}");
    Ok(())
}
