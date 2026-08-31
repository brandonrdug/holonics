//! The specialization wheel, rolled, and what it admits.
//!
//! `a_p` of a specialized Mestre quartic depends only on `T mod p`. Each prime receiver therefore
//! cuts specialization space into `p` classes and can say nothing finer — it cannot reconstruct
//! `T`'s interior, only its own face of it. The wheel's **motion** is the law by which those faces
//! compose: distinct receivers see disjoint information, so the Chinese Remainder Theorem carries
//! their partitions into one composite partition, and a composite class is a coincidence held at
//! every receiver simultaneously. Rolling is that composition performed one receiver at a time.
//!
//! This is why the wheel is not a lookup table. A high-rank specialization is a *coincidence
//! across the partition* — each realizer beyond the forced eleven arrives from a quadratic
//! section, contributing exactly when a congruence condition holds, and those conditions couple
//! every receiver at once. The rolled wheel admits only classes that survive all of them and turns
//! past the rest without ever building a curve.
//!
//! **Nothing here is decided by a float.** Cells are `⌊M·(#E − p − 1)/#E⌋`, an exact integer
//! division of the crossing ratio; the roll sums integers; the class order is an integer order;
//! weight is the exact integer `max(|c4|^3, c6^2)` compared against an integer ceiling. One float
//! converts the leaderboard's published decimal column into that ceiling — rounding up, so it can
//! never reject a genuine record — and one more prints a report line. Neither decides anything.
//!
//! `--validate` grades the roll against a published record: leaderboard curve #159 is the
//! specialization `T = 2454` of its family, and the wheel must rate its class highly unprompted.

use holonic_engine::{
    CudaRealizerReceiverFamily as ReceiverFamily, QuarticChart, RealizerSextuple,
    ReceiverPartition, ResidentRealizerSearch, ResidualReceivers, RolledWheel, WheelReceiver,
    complete_to_sextuple, exact_square_root, height_ceiling_from_published_log, homogeneous_value,
    independence_certificate, is_negation_symmetric, minimalise, partitions_from_traces,
    primes_upto,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use std::collections::BTreeSet;
use std::env;
use std::time::{Duration, Instant};

/// The frontier as the leaderboard publishes it: the smallest `log(naive height)` on record at
/// rank at least `r`. Read once, converted to exact integers immediately.
const PUBLISHED_FRONTIER: [(usize, f64); 11] = [
    (12, 69.3388),
    (13, 75.7603),
    (14, 85.1893),
    (15, 118.7702),
    (16, 125.3336),
    (17, 136.7901),
    (18, 159.9746),
    (19, 166.8295),
    (20, 200.2833),
    (21, 212.1831),
    (22, 239.3849),
];

fn argument<T: std::str::FromStr>(arguments: &[String], flag: &str, fallback: T) -> T {
    arguments
        .iter()
        .position(|a| a == flag)
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(fallback)
}

/// For the report line only. Never compared against, never used to decide.
fn report_log(value: &BigInt) -> f64 {
    let bits = value.bits();
    if bits == 0 {
        return f64::NEG_INFINITY;
    }
    if bits <= 52 {
        let small: i128 = value.try_into().unwrap_or(i128::MAX);
        return (small as f64).abs().ln();
    }
    let shift = bits - 52;
    let head: i128 = (value >> shift).try_into().unwrap_or(i128::MAX);
    (head as f64).abs().ln() + shift as f64 * std::f64::consts::LN_2
}

fn receiver_partitions(
    family: &RealizerSextuple,
    primes: &[u64],
    search: Option<&ResidentRealizerSearch>,
) -> Vec<ReceiverPartition> {
    if let Some(search) = search {
        let prepared = family.wheel_preparation(primes);
        let receivers: Vec<WheelReceiver> = prepared
            .iter()
            .map(|p| WheelReceiver {
                prime: p.prime,
                polynomials: p.polynomials.clone(),
                degree: p.degree,
                signs: p.signs.clone(),
            })
            .collect();
        if let Ok(traces) = search.wheel_traces(&receivers) {
            return partitions_from_traces(&prepared, &traces);
        }
    }
    family.receiver_partitions(primes)
}

struct Graded {
    rank: usize,
    key: BigInt,
    realizers: usize,
}

#[allow(clippy::too_many_arguments)]
fn grade(
    family: &RealizerSextuple,
    parameter: i64,
    search: &ResidentRealizerSearch,
    small: &[u64],
    receiver_primes: &[u64],
    certificate_primes: &[u64],
    integral_bound: i64,
    denominator_bound: i64,
    numerator_bound: i64,
    weight_ceiling: &BigInt,
) -> Option<Graded> {
    let t = BigRational::from_integer(BigInt::from(parameter));
    let remainder = family.remainder_at(&t);
    if remainder.coefficient[4].is_zero() {
        return None;
    }
    let quartic = remainder.integral(small);
    let (c4, c6) = quartic.invariants();
    if c4.is_zero() && c6.is_zero() {
        return None;
    }
    let minimal = minimalise(&c4, &c6, small);
    if minimal.discriminant.is_zero() {
        return None;
    }
    // Exact integer gate. Above the frontier's heaviest line there is no record to take at any
    // rank, so the card is never touched.
    let key = minimal.naive_height_key();
    if &key >= weight_ceiling {
        return None;
    }
    let receivers = ReceiverFamily::declare(&quartic, receiver_primes);
    let mut pairs: Vec<(i64, i64)> = search
        .sweep_integral(&receivers, -integral_bound, 2 * integral_bound + 1, 1 << 18)
        .ok()?
        .survivors;
    if denominator_bound > 1 {
        if let Ok(sweep) = search.sweep_rational(
            &receivers,
            2,
            denominator_bound - 1,
            -numerator_bound,
            2 * numerator_bound + 1,
            1 << 18,
        ) {
            pairs.extend(sweep.survivors);
        }
    }
    let mut admitted: Vec<(BigInt, BigInt)> = remainder
        .forced_realizers
        .iter()
        .map(|(x, _)| (x.numer().clone(), x.denom().clone()))
        .collect();
    let mut seen: BTreeSet<(i64, i64)> = BTreeSet::new();
    for (n, d) in pairs {
        let (mut a, mut b) = (n.unsigned_abs(), d.unsigned_abs());
        while b != 0 {
            let t = a % b;
            a = b;
            b = t;
        }
        let g = a.max(1) as i64;
        let reduced = (n / g, d / g);
        if !seen.insert(reduced) {
            continue;
        }
        let bn = BigInt::from(reduced.0);
        let bd = BigInt::from(reduced.1);
        if exact_square_root(&homogeneous_value(&quartic, &bn, &bd)).is_some() {
            admitted.push((bn, bd));
        }
    }
    let base = remainder.forced_realizers[0].clone();
    let chart = QuarticChart::through(&remainder.coefficient, &base)?;
    let mut carried = Vec::new();
    for (n, d) in admitted.iter() {
        let x = BigRational::new(n.clone(), d.clone());
        let Some(root) = exact_square_root(&homogeneous_value(&quartic, n, d)) else {
            continue;
        };
        let y = BigRational::new(root, d.clone() * d.clone()) / quartic.scale.clone();
        if let Some(point) = chart.carry(&x, &y) {
            if chart.curve.contains(&point.0, &point.1) {
                carried.push(point);
            }
        }
    }
    let realizers = carried.len();
    let certificate = independence_certificate(&chart.curve, &carried, 5, certificate_primes);
    Some(Graded {
        rank: certificate.rank_lower_bound,
        key,
        realizers,
    })
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    let validate = arguments.iter().any(|a| a == "--validate");
    let wheel_prime_bound: u64 = argument(&arguments, "--wheel-primes", 1200);
    let roll_ceiling: u64 = argument(&arguments, "--roll-ceiling", 2_000_000);
    let classes: usize = argument(&arguments, "--classes", 64);
    let turns: i64 = argument(&arguments, "--turns", 6);
    let keep: usize = argument(&arguments, "--keep", 150);
    let head_bound: i64 = argument(&arguments, "--head-bound", 60);
    let seconds: u64 = argument(&arguments, "--seconds", 150);
    let report_rank: usize = argument(&arguments, "--report-rank", 15);
    let integral_bound: i64 = argument(&arguments, "--integral-bound", 2_000_000);
    let denominator_bound: i64 = argument(&arguments, "--denominator-bound", 300);
    let numerator_bound: i64 = argument(&arguments, "--numerator-bound", 150_000);

    // The frontier, converted to exact integers at the boundary and never touched by a float again.
    let frontier: Vec<(usize, BigInt)> = PUBLISHED_FRONTIER
        .iter()
        .map(|(r, published)| (*r, height_ceiling_from_published_log(*published)))
        .collect();
    let weight_ceiling = frontier
        .iter()
        .map(|(_, c)| c.clone())
        .max()
        .unwrap_or_else(BigInt::zero);

    let small = primes_upto(20_000);
    let wheel_primes = primes_upto(wheel_prime_bound);
    let receiver_primes: Vec<u64> = primes_upto(200)
        .into_iter()
        .filter(|&p| p >= 3)
        .take(40)
        .collect();
    let certificate_primes = primes_upto(4000);
    let card = ResidentRealizerSearch::mount().ok();

    if validate {
        let published = RealizerSextuple::found(
            [-1146, -2304, -654, 3054, 2880, -1830]
                .map(|v| BigRational::from_integer(BigInt::from(v))),
        )
        .expect("on the variety");
        let started = Instant::now();
        let partitions = receiver_partitions(&published, &wheel_primes, card.as_ref());
        let build = started.elapsed().as_secs_f64();
        let host = published.receiver_partitions(&wheel_primes);
        assert_eq!(
            partitions, host,
            "the card and the host must return one wheel"
        );
        let (rolled, deferred) = RolledWheel::roll(&partitions, roll_ceiling);
        let residual = ResidualReceivers {
            partitions: partitions
                .iter()
                .filter(|p| deferred.contains(&p.prime))
                .cloned()
                .collect(),
        };
        println!(
            "receiver partitions : {} receivers, built in {build:.2} s (card and host agree exactly)",
            partitions.len()
        );
        println!(
            "rolled              : modulus {} composing receivers {:?}",
            rolled.modulus, rolled.receivers
        );
        println!(
            "deferred to residual: {} receivers",
            residual.partitions.len()
        );

        let probe = 2454i64;
        let probe_class = probe.rem_euclid(rolled.modulus as i64) as u64;
        let probe_score = rolled.score[probe_class as usize];
        let better = rolled.score.iter().filter(|v| **v > probe_score).count();
        println!(
            "\nthe published T = 2454 lies in composite class {probe_class} of {}, which the exact \
             integer order rates above {} of them ({:.2}%)",
            rolled.modulus,
            rolled.modulus as usize - better - 1,
            100.0 * (rolled.modulus as f64 - better as f64) / rolled.modulus as f64
        );
        let full = probe_score + residual.score(probe);
        let sampled = 6000i64;
        let rivals = (1..=sampled)
            .filter(|t| {
                rolled.score[(t.rem_euclid(rolled.modulus as i64)) as usize] + residual.score(*t)
                    > full
            })
            .count();
        println!(
            "against the first {sampled} specializations it ranks {} — exact integers, no logarithm \
             anywhere in the ordering",
            rivals + 1
        );
        if arguments.iter().any(|a| a == "--dump-scores") {
            let mut out = String::new();
            for t in 1..=sampled {
                let score = rolled.score[(t.rem_euclid(rolled.modulus as i64)) as usize]
                    + residual.score(t);
                out.push_str(&format!("{t} {score}\n"));
            }
            std::fs::write("wheel_scores.txt", out).expect("dump");
            println!("exact integer wheel scores written to wheel_scores.txt");
        }
        return;
    }

    let Some(search) = card else {
        eprintln!("the card refused the mount");
        std::process::exit(1);
    };
    let deadline = Instant::now() + Duration::from_secs(seconds);
    let mut families = 0u64;
    let mut graded = 0u64;
    let mut visited = 0u64;
    let mut ranks = [0u64; 40];
    let mut records = 0u64;
    let mut best: Vec<(usize, BigInt, String, i64)> = Vec::new();

    'outer: for a in -head_bound..=head_bound {
        for b in a + 1..=head_bound {
            for c in b + 1..=head_bound {
                for d in c + 1..=head_bound {
                    if Instant::now() >= deadline {
                        break 'outer;
                    }
                    let head = [a, b, c, d].map(|v| BigRational::from_integer(BigInt::from(v)));
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
                        families += 1;
                        let partitions =
                            receiver_partitions(&working, &wheel_primes, Some(&search));
                        let (rolled, deferred) = RolledWheel::roll(&partitions, roll_ceiling);
                        let residual = ResidualReceivers {
                            partitions: partitions
                                .into_iter()
                                .filter(|p| deferred.contains(&p.prime))
                                .collect(),
                        };
                        // The wheel turns: only admitted classes are visited, and inside a class
                        // the parameter advances by the composite modulus.
                        let mut candidates: Vec<(i64, i64)> = Vec::new();
                        for class in rolled.admitted_classes(classes) {
                            for turn in 0..turns {
                                let parameter = class as i64 + turn * rolled.modulus as i64;
                                if parameter == 0 {
                                    continue;
                                }
                                candidates.push((
                                    rolled.score[class as usize] + residual.score(parameter),
                                    parameter,
                                ));
                            }
                        }
                        candidates.sort_by(|x, y| y.0.cmp(&x.0));
                        for &(_, parameter) in candidates.iter().take(keep) {
                            if Instant::now() >= deadline {
                                break 'outer;
                            }
                            visited += 1;
                            let Some(result) = grade(
                                &working,
                                parameter,
                                &search,
                                &small,
                                &receiver_primes,
                                &certificate_primes,
                                integral_bound,
                                denominator_bound,
                                numerator_bound,
                                &weight_ceiling,
                            ) else {
                                continue;
                            };
                            graded += 1;
                            if result.rank < 40 {
                                ranks[result.rank] += 1;
                            }
                            if result.rank < report_rank {
                                continue;
                            }
                            let beaten = frontier
                                .iter()
                                .filter(|(r, ceiling)| *r <= result.rank && result.key < *ceiling)
                                .map(|(r, _)| *r)
                                .max();
                            let values: Vec<String> =
                                working.values().iter().map(|v| v.to_string()).collect();
                            let note = match beaten {
                                Some(r) => {
                                    records += 1;
                                    format!(
                                        " *** RECORD: rank {} beats the rank-{r} line ***",
                                        result.rank
                                    )
                                }
                                None => String::new(),
                            };
                            println!(
                                "rank {:>2}  log weight {:8.4}  realizers {:>3}  T = {parameter}  \
                                 [{}]{note}",
                                result.rank,
                                report_log(&result.key),
                                result.realizers,
                                values.join(", ")
                            );
                            best.push((result.rank, result.key, values.join(", "), parameter));
                        }
                    }
                }
            }
        }
    }

    println!("\n--- rolled sweep closed ---");
    println!("families off the variety : {families}");
    println!("classes visited          : {visited}");
    println!("passed the integer gate  : {graded}");
    println!("records taken            : {records}");
    print!("rank census              :");
    for (rank, count) in ranks.iter().enumerate() {
        if *count > 0 {
            print!(" {rank}:{count}");
        }
    }
    println!();
    best.sort_by(|x, y| y.0.cmp(&x.0).then(x.1.cmp(&y.1)));
    for (rank, key, values, parameter) in best.iter().take(12) {
        println!(
            "  best  rank {rank:>2}  log weight {:8.4}  T = {parameter}  [{values}]",
            report_log(key)
        );
    }
}

fn gcd_big(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = a.clone();
    let mut b = b.clone();
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a
}
