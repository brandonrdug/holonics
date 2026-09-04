//! Solve every linear section of a published realizer family, then certify the rank the family
//! carries over its whole base — float-free, and with no search.
//!
//! A specialization is a cut through the elliptic surface `y^2 = r(x, T)`. What every fibre
//! inherits is the Mordell–Weil group of the surface over `Q(T)`, and its sections are what
//! [`RealizerSextuple::linear_sections`] **solves**: along `x = αT + β` the family polynomial
//! splits into twelve known linear forms, the completed square forces `g ∓ h` to be complementary
//! six-subsets of them, and the coefficient ladder hands two univariate polynomials to the exact
//! rational-root finder. Mestre's twelve realizers are the degenerate sections `x = a_i ± T`;
//! every other solved section is a direction the construction did not force.
//!
//! The certificate is then read at fibres fixed **before** any family is seen, so none is chosen
//! for its answer: at each probe the forced realizers and the solved sections are evaluated, carried
//! to a Weierstrass model, and their independence is decided by reduction at declared prime
//! receivers (`independence_certificate`) — no height pairing, no regulator, no float. The family
//! rank is the minimum over the probes.
//!
//! **Measured 2026-08-27.** The root finder this solver stood on until today was the Sturm
//! half-integer census from an absolute Cauchy bound; on the first published family it did not
//! return in 175 seconds. The p-adic lifting finder (`rational_roots_by_lifting`) returns both
//! published families in under eight seconds. Every returned section is verified: `r` restricted
//! to it is a perfect square in `Q[T]`.

use holonic_engine::{QuarticChart, RealizerSextuple, independence_certificate, primes_upto};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::fs;
use std::time::Instant;

/// Fibres fixed here, before any family is seen.
const PROBE_FIBRES: [i64; 4] = [101, 1009, 2411, 3001];

const OUTPUT: &str = ".local/artifacts/the_sections_are_solved_and_the_family_rank_is_certified";

fn rational(values: [i64; 6]) -> [BigRational; 6] {
    values.map(|v| BigRational::from_integer(BigInt::from(v)))
}

fn rational_square_root(value: &BigRational) -> Option<BigRational> {
    if value.is_negative() {
        return None;
    }
    let n = value.numer().sqrt();
    let d = value.denom().sqrt();
    if &n * &n == *value.numer() && &d * &d == *value.denom() {
        Some(BigRational::new(n, d))
    } else {
        None
    }
}

fn evaluate(coefficient: &[BigRational], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for c in coefficient.iter().rev() {
        acc = acc * x + c;
    }
    acc
}

struct FamilyReturn {
    label: String,
    values: Vec<String>,
    sections: Vec<(String, String)>,
    solve_seconds: f64,
    probe_ranks: Vec<(i64, usize, usize, bool)>,
    family_rank: usize,
}

fn main() {
    let published: [(&str, [i64; 6]); 3] = [
        (
            "leaderboard #159 (rank 17)",
            [-1146, -2304, -654, 3054, 2880, -1830],
        ),
        (
            "leaderboard #161 (rank 18)",
            [348, -600, -216, 492, 876, -900],
        ),
        (
            "leaderboard #280 (rank 19)",
            [0, 1075, 1394, 2291, 4186, 4824],
        ),
    ];
    let certificate_primes = primes_upto(4000);
    let mut returns = Vec::new();
    for (label, values) in published {
        let family = RealizerSextuple::found_after_centring(rational(values))
            .expect("published sextuples lie on the variety");
        let started = Instant::now();
        let sections = family.linear_sections();
        let solve_seconds = started.elapsed().as_secs_f64();
        let remainder_polynomials = family.remainder_polynomials();
        let mut probe_ranks = Vec::new();
        for parameter in PROBE_FIBRES {
            let t = BigRational::from_integer(BigInt::from(parameter));
            let remainder = family.remainder_at(&t);
            if remainder.coefficient[4].is_zero() {
                continue;
            }
            let mut realizers: Vec<(BigRational, BigRational)> = remainder.forced_realizers.clone();
            let mut section_realizers = 0usize;
            for section in sections.iter() {
                let x = &section.slope * &t + &section.intercept;
                let value = evaluate(&remainder.coefficient, &x);
                // the section is a section: `r` along it is a square in `Q[T]`, so a square here
                let composed = family.remainder_along(
                    &remainder_polynomials,
                    &section.slope,
                    &section.intercept,
                );
                assert_eq!(
                    value,
                    evaluate(&composed, &t),
                    "the composed polynomial disagrees with the fibre"
                );
                let Some(y) = rational_square_root(&value) else {
                    panic!("a solved section returned a non-square at T = {parameter}");
                };
                if !realizers.iter().any(|(rx, _)| *rx == x) {
                    realizers.push((x, y));
                    section_realizers += 1;
                }
            }
            let base = remainder.forced_realizers[0].clone();
            let Some(chart) = QuarticChart::through(&remainder.coefficient, &base) else {
                continue;
            };
            let mut carried = Vec::new();
            for (x, y) in realizers.iter() {
                if let Some(point) = chart.carry(x, y) {
                    assert!(
                        chart.curve.contains(&point.0, &point.1),
                        "carried realizer left the curve"
                    );
                    carried.push(point);
                }
            }
            let certificate =
                independence_certificate(&chart.curve, &carried, 5, &certificate_primes);
            probe_ranks.push((
                parameter,
                certificate.rank_lower_bound,
                section_realizers,
                certificate.torsion_free,
            ));
        }
        let family_rank = probe_ranks.iter().map(|p| p.1).min().unwrap_or(0);
        returns.push(FamilyReturn {
            label: label.to_owned(),
            values: family.values().iter().map(|v| v.to_string()).collect(),
            sections: sections
                .iter()
                .map(|s| (s.slope.to_string(), s.intercept.to_string()))
                .collect(),
            solve_seconds,
            probe_ranks,
            family_rank,
        });
    }

    for r in &returns {
        println!(
            "{}\n  centred sextuple [{}]\n  solved linear sections: {} in {:.2} s",
            r.label,
            r.values.join(", "),
            r.sections.len(),
            r.solve_seconds
        );
        for (slope, intercept) in &r.sections {
            println!("    x(T) = ({slope})·T + ({intercept})");
        }
        for (t, rank, added, torsion_free) in &r.probe_ranks {
            println!(
                "  probe T={t}: certified rank >= {rank} (section realizers added {added}, torsion-free witnessed {torsion_free})"
            );
        }
        println!("  FAMILY RANK OVER Q(T) >= {}\n", r.family_rank);
    }
    fs::create_dir_all(OUTPUT).expect("output directory");
    let mut receipt = String::from("{\n  \"families\": [\n");
    for (i, r) in returns.iter().enumerate() {
        receipt.push_str(&format!(
            "    {{\"label\": \"{}\", \"sextuple\": [{}], \"linear_sections\": [{}], \"solve_seconds\": {:.3}, \"probes\": [{}], \"family_rank_lower_bound\": {}}}{}\n",
            r.label,
            r.values.iter().map(|v| format!("\"{v}\"")).collect::<Vec<_>>().join(", "),
            r.sections
                .iter()
                .map(|(s, b)| format!("{{\"slope\": \"{s}\", \"intercept\": \"{b}\"}}"))
                .collect::<Vec<_>>()
                .join(", "),
            r.solve_seconds,
            r.probe_ranks
                .iter()
                .map(|(t, rank, added, tf)| format!(
                    "{{\"T\": {t}, \"rank_lower_bound\": {rank}, \"section_realizers\": {added}, \"torsion_free\": {tf}}}"
                ))
                .collect::<Vec<_>>()
                .join(", "),
            r.family_rank,
            if i + 1 < returns.len() { "," } else { "" }
        ));
    }
    receipt.push_str("  ],\n  \"probe_fibres\": [101, 1009, 2411, 3001],\n  \"certificate_receivers\": \"primes below 4000, torsion prime 5\",\n  \"root_finder\": \"rational_roots_by_lifting (one prime receiver, Newton lift, rational reconstruction, exact verification)\"\n}\n");
    fs::write(format!("{OUTPUT}/receipt.json"), receipt).expect("receipt");
    println!("artifact={OUTPUT}/receipt.json");
}
