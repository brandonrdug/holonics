//! Measure the rank a realizer family carries over its whole base, not the rank of one fibre.
//!
//! A specialization is a cut. The **family rank** — the Mordell–Weil rank of the surface over
//! `Q(T)` — is the invariant, and it is inherited by *every* fibre at once, where a lucky
//! specialization lifts exactly one. Mestre's construction forces twelve sections and so carries
//! rank eleven generically; the record constructions carry seventeen or eighteen. That difference,
//! not the specialization search, is what separates rank 20 from rank 30.
//!
//! It is measurable and exact. A section of the surface lands in every fibre, so a direction it
//! contributes is present at *every* `T`; a sporadic realizer is present at one. Therefore
//!
//! ```text
//!     family rank  =  min over generic fibres of the exactly certified rank
//! ```
//!
//! and the minimum is taken over fibres chosen before anything is measured, so no fibre is
//! selected for its answer.
//!
//! Measured this way on the sextuple the leaderboard published for curve #159: Mestre's twelve
//! forced realizers certify rank 11 at every fibre, and six further sections with **linear**
//! `x(T)` and denominator 53 — extracted from the surface sweep's residual population, not
//! supplied — certify rank 12 at every fibre. That family carries twelve, not eleven.

use holonic_engine::{
    CudaRealizerReceiverFamily as ReceiverFamily, QuarticChart, RealizerSextuple,
    ResidentRealizerSearch, complete_to_sextuple, exact_square_root, homogeneous_value,
    independence_certificate, is_negation_symmetric, primes_upto,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use std::collections::BTreeSet;
use std::env;
use std::time::{Duration, Instant};

/// Fibres are fixed here, before any family is seen, so none is chosen for its answer.
const PROBE_FIBRES: [i64; 4] = [101, 1009, 2411, 3001];

fn argument<T: std::str::FromStr>(arguments: &[String], flag: &str, fallback: T) -> T {
    arguments
        .iter()
        .position(|a| a == flag)
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(fallback)
}

/// The exactly certified rank of one fibre, from the family's forced realizers plus whatever the
/// card finds. Returns `None` when the fibre is degenerate.
#[allow(clippy::too_many_arguments)]
fn fibre_rank(
    family: &RealizerSextuple,
    parameter: i64,
    search: &ResidentRealizerSearch,
    small: &[u64],
    receiver_primes: &[u64],
    certificate_primes: &[u64],
    integral_bound: i64,
    denominator_bound: i64,
    numerator_bound: i64,
) -> Option<usize> {
    let t = BigRational::from_integer(BigInt::from(parameter));
    let remainder = family.remainder_at(&t);
    if remainder.coefficient[4].is_zero() {
        return None;
    }
    let quartic = remainder.integral(small);
    let declared = ReceiverFamily::declare(&quartic, receiver_primes);
    let mut pairs: Vec<(i64, i64)> = search
        .sweep_integral(&declared, -integral_bound, 2 * integral_bound + 1, 1 << 18)
        .ok()?
        .survivors;
    if denominator_bound > 1 {
        if let Ok(sweep) = search.sweep_rational(
            &declared,
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
    Some(independence_certificate(&chart.curve, &carried, 5, certificate_primes).rank_lower_bound)
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    let head_bound: i64 = argument(&arguments, "--head-bound", 60);
    let seconds: u64 = argument(&arguments, "--seconds", 150);
    let report: usize = argument(&arguments, "--report", 12);
    let integral_bound: i64 = argument(&arguments, "--integral-bound", 1_000_000);
    let denominator_bound: i64 = argument(&arguments, "--denominator-bound", 400);
    let numerator_bound: i64 = argument(&arguments, "--numerator-bound", 200_000);

    let small = primes_upto(20_000);
    let receiver_primes: Vec<u64> = primes_upto(200)
        .into_iter()
        .filter(|&p| p >= 3)
        .take(40)
        .collect();
    let certificate_primes = primes_upto(4000);
    let Ok(search) = ResidentRealizerSearch::mount() else {
        eprintln!("the card refused the mount");
        std::process::exit(1);
    };

    if arguments.iter().any(|a| a == "--validate") {
        let published = RealizerSextuple::found(
            [-1146, -2304, -654, 3054, 2880, -1830]
                .map(|v| BigRational::from_integer(BigInt::from(v))),
        )
        .expect("on the variety");
        print!("published family, rank by probe fibre:");
        let mut ranks = Vec::new();
        for parameter in PROBE_FIBRES {
            if let Some(rank) = fibre_rank(
                &published,
                parameter,
                &search,
                &small,
                &receiver_primes,
                &certificate_primes,
                integral_bound,
                denominator_bound,
                numerator_bound,
            ) {
                print!(" T={parameter}:{rank}");
                ranks.push(rank);
            }
        }
        println!();
        println!(
            "family rank carried over the whole base = {}",
            ranks.iter().min().copied().unwrap_or(0)
        );
        return;
    }

    let deadline = Instant::now() + Duration::from_secs(seconds);
    let mut families = 0u64;
    let mut census = [0u64; 40];
    let mut best: Vec<(usize, String)> = Vec::new();

    // **Integration by reflection.** Trace-zero integer sextuples are the root lattice `A_5`, whose
    // Weyl group is `S_6` acting by the reflections that transpose coordinates; negation extends it
    // to `S_6 × {±1}`. A family is a point of the *orbit space*, so enumerating tuples enumerates
    // each family up to 1440 times — visible in the first sweep, where one sextuple appeared in six
    // orderings. Sampling the box was worse: still a search, and it drew orderings, not orbits.
    //
    // So walk the fundamental domain: strictly increasing coordinates, shells of the norm form
    // `Σ a_i²` in increasing order, each orbit visited once. The norm is not an arbitrary ordering —
    // it drives the specialization's weight, so shells arrive in increasing height, which is the
    // order a record is won in.
    let mut visited: BTreeSet<Vec<i64>> = BTreeSet::new();
    'outer: for shell in 1..=head_bound {
        for a in -shell..=shell {
            for b in a + 1..=shell {
                for c in b + 1..=shell {
                    for d in c + 1..=shell {
                        if a.abs().max(b.abs()).max(c.abs()).max(d.abs()) != shell {
                            continue;
                        }
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
                            // the orbit representative under `S_6 × {±1}`
                            let mut canonical: Vec<i64> = working
                                .values()
                                .iter()
                                .map(|v| v.numer().try_into().unwrap_or(0))
                                .collect();
                            canonical.sort_unstable();
                            let mut negated: Vec<i64> = canonical.iter().map(|v| -v).collect();
                            negated.sort_unstable();
                            if negated < canonical {
                                canonical = negated;
                            }
                            if !visited.insert(canonical) {
                                continue;
                            }
                            families += 1;
                            let mut carried_rank = usize::MAX;
                            for parameter in PROBE_FIBRES {
                                if Instant::now() >= deadline {
                                    break 'outer;
                                }
                                match fibre_rank(
                                    &working,
                                    parameter,
                                    &search,
                                    &small,
                                    &receiver_primes,
                                    &certificate_primes,
                                    integral_bound,
                                    denominator_bound,
                                    numerator_bound,
                                ) {
                                    Some(rank) => carried_rank = carried_rank.min(rank),
                                    None => continue,
                                }
                                // a family already below the reporting line cannot recover: the
                                // minimum only falls
                                if carried_rank < report {
                                    break;
                                }
                            }
                            if carried_rank == usize::MAX {
                                continue;
                            }
                            if carried_rank < 40 {
                                census[carried_rank] += 1;
                            }
                            if carried_rank >= report {
                                let values: Vec<String> =
                                    working.values().iter().map(|v| v.to_string()).collect();
                                println!(
                                    "family rank {carried_rank:>2}   sextuple [{}]",
                                    values.join(", ")
                                );
                                best.push((carried_rank, values.join(", ")));
                            }
                        }
                    }
                }
            }
        }
    }

    println!("\n--- family-rank sweep closed ---");
    println!("families measured : {families}");
    print!("carried-rank census:");
    for (rank, count) in census.iter().enumerate() {
        if *count > 0 {
            print!(" {rank}:{count}");
        }
    }
    println!();
    best.sort_by(|x, y| y.0.cmp(&x.0));
    for (rank, values) in best.iter().take(12) {
        println!("  best  family rank {rank:>2}  [{values}]");
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
