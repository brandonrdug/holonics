//! Walk the realizer variety and count, for each family, the linear sections its surface carries
//! — then certify the family rank of the richest families, float-free, at fibres fixed in advance.
//!
//! The rank a Mestre family carries over `Q(T)` is inherited by every fibre. Mestre's twelve
//! forced realizers carry eleven; the three record families on the leaderboard each carry exactly
//! six further linear sections, which raise the family rank to twelve
//! (`the_sections_are_solved_and_the_family_rank_is_certified`). The question this driver asks
//! is whether the variety `e_1 = 0, 2e_5 = e_2 e_3` holds families with **more** linear sections
//! than those, because every extra independent section is a rank every specialization inherits
//! before any sporadic realizer is searched for.
//!
//! The walk is the fundamental domain of `S_6 × {±1} × Q^×` on trace-zero integer heads
//! (strictly increasing coordinates, shells of the sup norm in increasing order), completed to
//! the variety by [`complete_to_sextuple`] and reduced to primitive content — scaling the six
//! values is `x -> λx, T -> λT` on the surface, one family — so each family is visited once. For each family the
//! solver returns its linear sections; the census tallies section counts; families with at least
//! `--report` sections are certified by reduction at declared prime receivers at the probe fibres
//! `T ∈ {101, 1009, 2411, 3001}`. Nothing is ranked by a float; the census is a population and
//! the certificate is exact.

use holonic_engine::{
    QuarticChart, RealizerSextuple, complete_to_sextuple, independence_certificate,
    is_negation_symmetric, primes_upto,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const PROBE_FIBRES: [i64; 4] = [101, 1009, 2411, 3001];
const OUTPUT: &str = "output/the_section_census_walks_the_realizer_variety";

fn argument<T: std::str::FromStr>(arguments: &[String], flag: &str, fallback: T) -> T {
    arguments
        .iter()
        .position(|a| a == flag)
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(fallback)
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

fn gcd_big(a: &BigInt, b: &BigInt) -> BigInt {
    let (mut a, mut b) = (a.clone(), b.clone());
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a
}

/// The family rank certified from forced realizers and solved sections at the probe fibres.
fn certify(family: &RealizerSextuple, certificate_primes: &[u64]) -> (usize, Vec<(i64, usize)>) {
    let sections = family.linear_sections();
    let mut probes = Vec::new();
    for parameter in PROBE_FIBRES {
        let t = BigRational::from_integer(BigInt::from(parameter));
        let remainder = family.remainder_at(&t);
        if remainder.coefficient[4].is_zero() {
            continue;
        }
        let mut realizers = remainder.forced_realizers.clone();
        for section in sections.iter() {
            let x = &section.slope * &t + &section.intercept;
            let Some(y) = rational_square_root(&evaluate(&remainder.coefficient, &x)) else {
                continue;
            };
            if !realizers.iter().any(|(rx, _)| *rx == x) {
                realizers.push((x, y));
            }
        }
        let base = remainder.forced_realizers[0].clone();
        let Some(chart) = QuarticChart::through(&remainder.coefficient, &base) else {
            continue;
        };
        let carried: Vec<(BigRational, BigRational)> = realizers
            .iter()
            .filter_map(|(x, y)| chart.carry(x, y))
            .collect();
        let certificate = independence_certificate(&chart.curve, &carried, 5, certificate_primes);
        probes.push((parameter, certificate.rank_lower_bound));
    }
    let family_rank = probes.iter().map(|p| p.1).min().unwrap_or(0);
    (family_rank, probes)
}

struct Census {
    families: u64,
    sections: [u64; 64],
    rich: Vec<(usize, usize, Vec<(i64, usize)>, Vec<String>)>,
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    let head_bound: i64 = argument(&arguments, "--head-bound", 40);
    let seconds: u64 = argument(&arguments, "--seconds", 150);
    let report: usize = argument(&arguments, "--report", 8);
    let workers: usize = argument(
        &arguments,
        "--workers",
        thread::available_parallelism()
            .map(|c| c.get())
            .unwrap_or(1),
    );
    let deadline = Instant::now() + Duration::from_secs(seconds);
    let certificate_primes = Arc::new(primes_upto(4000));

    // the fundamental domain, in shells, each orbit once
    let mut heads: Vec<[i64; 4]> = Vec::new();
    for shell in 1..=head_bound {
        for a in -shell..=shell {
            for b in a + 1..=shell {
                for c in b + 1..=shell {
                    for d in c + 1..=shell {
                        if a.abs().max(b.abs()).max(c.abs()).max(d.abs()) != shell {
                            continue;
                        }
                        heads.push([a, b, c, d]);
                    }
                }
            }
        }
    }
    let heads = Arc::new(heads);
    let next = Arc::new(AtomicUsize::new(0));
    let visited: Arc<Mutex<BTreeSet<Vec<i64>>>> = Arc::new(Mutex::new(BTreeSet::new()));
    let census = Arc::new(Mutex::new(Census {
        families: 0,
        sections: [0; 64],
        rich: Vec::new(),
    }));
    let started = Instant::now();
    thread::scope(|scope| {
        for _ in 0..workers.max(1) {
            let heads = Arc::clone(&heads);
            let next = Arc::clone(&next);
            let visited = Arc::clone(&visited);
            let census = Arc::clone(&census);
            let certificate_primes = Arc::clone(&certificate_primes);
            scope.spawn(move || {
                loop {
                    if Instant::now() >= deadline {
                        break;
                    }
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(head) = heads.get(index) else {
                        break;
                    };
                    let head = head.map(|v| BigRational::from_integer(BigInt::from(v)));
                    for sextuple in complete_to_sextuple(head) {
                        if is_negation_symmetric(&sextuple) {
                            continue;
                        }
                        let mut common = BigInt::from(1);
                        for v in sextuple.values().iter() {
                            let g = gcd_big(&common, v.denom());
                            common = &common * v.denom() / g;
                        }
                        let scaled: Vec<BigRational> = sextuple
                            .values()
                            .iter()
                            .map(|v| v * BigRational::from_integer(common.clone()))
                            .collect();
                        let mut six = std::array::from_fn(|_| BigRational::zero());
                        six.clone_from_slice(&scaled[..6]);
                        let Ok(working) = RealizerSextuple::found(six) else {
                            continue;
                        };
                        let mut canonical: Vec<i64> = working
                            .values()
                            .iter()
                            .map(|v| v.numer().try_into().unwrap_or(0))
                            .collect();
                        // scaling `(a_i) -> (λ a_i)` is `x -> λx, T -> λT` on the surface: one family
                        let content = canonical.iter().fold(0i64, |g, v| {
                            let (mut a, mut b) = (g.abs(), v.abs());
                            while b != 0 {
                                let t = a % b;
                                a = b;
                                b = t;
                            }
                            a
                        });
                        if content > 1 {
                            for v in canonical.iter_mut() {
                                *v /= content;
                            }
                        }
                        canonical.sort_unstable();
                        let mut negated: Vec<i64> = canonical.iter().map(|v| -v).collect();
                        negated.sort_unstable();
                        if negated < canonical {
                            canonical = negated;
                        }
                        if !visited.lock().expect("visited").insert(canonical) {
                            continue;
                        }
                        let sections = working.linear_sections();
                        let count = sections.len();
                        let mut certified = None;
                        if count >= report {
                            certified = Some(certify(&working, &certificate_primes));
                        }
                        let mut c = census.lock().expect("census");
                        c.families += 1;
                        if count < 64 {
                            c.sections[count] += 1;
                        }
                        if let Some((rank, probes)) = certified {
                            let values = working.values().iter().map(|v| v.to_string()).collect();
                            c.rich.push((count, rank, probes, values));
                        }
                    }
                }
            });
        }
    });
    let elapsed = started.elapsed().as_secs_f64();
    let census = census.lock().expect("census");
    println!(
        "families measured: {} in {:.1} s on {} workers (heads visited {} of {})",
        census.families,
        elapsed,
        workers,
        next.load(Ordering::Relaxed).min(heads.len()),
        heads.len()
    );
    print!("linear-section census:");
    for (count, families) in census.sections.iter().enumerate() {
        if *families > 0 {
            print!(" {count}:{families}");
        }
    }
    println!();
    let mut rich = census.rich.clone();
    rich.sort_by(|a, b| b.1.cmp(&a.1).then(b.0.cmp(&a.0)));
    for (count, rank, probes, values) in rich.iter().take(16) {
        println!(
            "  sections {count:>2}  FAMILY RANK >= {rank:>2}  probes {:?}  sextuple [{}]",
            probes,
            values.join(", ")
        );
    }
    fs::create_dir_all(OUTPUT).expect("output directory");
    let receipt = format!(
        "{{\n  \"families\": {},\n  \"elapsed_seconds\": {:.1},\n  \"workers\": {},\n  \"head_bound\": {},\n  \"section_census\": {{{}}},\n  \"report_threshold\": {},\n  \"rich\": [\n{}\n  ]\n}}\n",
        census.families,
        elapsed,
        workers,
        head_bound,
        census
            .sections
            .iter()
            .enumerate()
            .filter(|(_, f)| **f > 0)
            .map(|(c, f)| format!("\"{c}\": {f}"))
            .collect::<Vec<_>>()
            .join(", "),
        report,
        rich.iter()
            .map(|(count, rank, probes, values)| format!(
                "    {{\"sections\": {count}, \"family_rank_lower_bound\": {rank}, \"probes\": [{}], \"sextuple\": [{}]}}",
                probes
                    .iter()
                    .map(|(t, r)| format!("{{\"T\": {t}, \"rank_lower_bound\": {r}}}"))
                    .collect::<Vec<_>>()
                    .join(", "),
                values.iter().map(|v| format!("\"{v}\"")).collect::<Vec<_>>().join(", ")
            ))
            .collect::<Vec<_>>()
            .join(",\n")
    );
    fs::write(format!("{OUTPUT}/receipt.json"), receipt).expect("receipt");
    println!("artifact={OUTPUT}/receipt.json");
}
