//! Sweep the elliptic surface once; read rank off its fibre populations.
//!
//! A Mestre family is one body — the elliptic surface `y^2 = r(x, T)` — and `T` is a fibration of
//! it, not an index into a list of curves. A realizer of the fibre over `T` is a point of the
//! surface that landed there. So the population which decides a fibre's rank is measured by
//! sweeping the surface and **coarse-graining its realizers by the fibration**, which is an exact
//! count of caused incidence, with no score, no weight, and no float standing between the sweep
//! and the answer.
//!
//! That is the correction to the wheel. A wheel of prime receivers partitions the parameter and
//! rates each class, but the rating is a soft per-receiver shadow: rolled over the small primes it
//! places the published rank-17 specialization at only the 62nd percentile, so pruning on it
//! discards the curve it exists to find. The fibration is the partition that actually carries the
//! object, because the thing being counted in each cell *is* the realizer population.
//!
//! Twelve realizers per fibre are forced by the family and carry no information. Every count above
//! twelve is a supported realizer the construction did not supply.

use holonic_engine::{
    CudaRealizerReceiverFamily as ReceiverFamily, QuarticChart, RealizerSextuple,
    ResidentRealizerSearch, WheelReceiver, complete_to_sextuple, exact_square_root,
    height_ceiling_from_published_log, homogeneous_value, independence_certificate,
    is_negation_symmetric, minimalise, primes_upto,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::time::{Duration, Instant};

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

/// gridDim.y is bounded; fibres are swept in sections of this many.
const FIBRE_SECTION: i64 = 32_768;

fn argument<T: std::str::FromStr>(arguments: &[String], flag: &str, fallback: T) -> T {
    arguments
        .iter()
        .position(|a| a == flag)
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(fallback)
}

/// Report line only.
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

/// Count the surface's realizers in each fibre of a parameter window.
fn fibre_populations(
    family: &RealizerSextuple,
    search: &ResidentRealizerSearch,
    receivers: &[WheelReceiver],
    fibre_bound: i64,
    abscissa_bound: i64,
) -> (BTreeMap<i64, Vec<i64>>, u128) {
    let mut populations: BTreeMap<i64, Vec<i64>> = BTreeMap::new();
    let mut examined = 0u128;
    let mut low = 1i64;
    while low <= fibre_bound {
        let span = (fibre_bound - low + 1).min(FIBRE_SECTION);
        let Ok(sweep) = search.sweep_surface(
            receivers,
            low,
            span,
            -abscissa_bound,
            2 * abscissa_bound + 1,
            1 << 22,
        ) else {
            low += span;
            continue;
        };
        examined += sweep.pairs_examined;
        for (abscissa, fibre) in sweep.survivors {
            populations.entry(fibre).or_default().push(abscissa);
        }
        low += span;
    }
    let _ = family;
    (populations, examined)
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
    weight_ceiling: Option<&BigInt>,
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
    let key = minimal.naive_height_key();
    if let Some(ceiling) = weight_ceiling {
        if &key >= ceiling {
            return None;
        }
    }
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
    let fibre_bound: i64 = argument(&arguments, "--fibre-bound", 6000);
    let abscissa_bound: i64 = argument(&arguments, "--abscissa-bound", 200_000);
    let refusal_prime_bound: u64 = argument(&arguments, "--refusal-primes", 180);
    let keep: usize = argument(&arguments, "--keep", 40);
    let head_bound: i64 = argument(&arguments, "--head-bound", 60);
    let seconds: u64 = argument(&arguments, "--seconds", 150);
    let report_rank: usize = argument(&arguments, "--report-rank", 15);
    let integral_bound: i64 = argument(&arguments, "--integral-bound", 2_000_000);
    let denominator_bound: i64 = argument(&arguments, "--denominator-bound", 300);
    let numerator_bound: i64 = argument(&arguments, "--numerator-bound", 150_000);

    let frontier: Vec<(usize, BigInt)> = PUBLISHED_FRONTIER
        .iter()
        .map(|(r, published)| (*r, height_ceiling_from_published_log(*published)))
        .collect();
    let weight_ceiling = frontier.iter().map(|(_, c)| c.clone()).max().unwrap();

    let small = primes_upto(20_000);
    let refusal_primes = primes_upto(refusal_prime_bound);
    let receiver_primes: Vec<u64> = primes_upto(200)
        .into_iter()
        .filter(|&p| p >= 3)
        .take(40)
        .collect();
    let certificate_primes = primes_upto(4000);
    // A short receiver family for the screen: enough to separate a promising fibre from a dull
    // one, far short of what a reported rank is allowed to rest on.
    let screen_primes = primes_upto(700);

    let Ok(search) = ResidentRealizerSearch::mount() else {
        eprintln!("the card refused the mount");
        std::process::exit(1);
    };

    let prepare = |family: &RealizerSextuple| -> Vec<WheelReceiver> {
        family
            .wheel_preparation(&refusal_primes)
            .into_iter()
            .map(|p| WheelReceiver {
                prime: p.prime,
                polynomials: p.polynomials,
                degree: p.degree,
                signs: p.signs,
            })
            .collect()
    };

    if validate {
        let published = RealizerSextuple::found(
            [-1146, -2304, -654, 3054, 2880, -1830]
                .map(|v| BigRational::from_integer(BigInt::from(v))),
        )
        .expect("on the variety");
        let receivers = prepare(&published);
        let started = Instant::now();
        let (populations, examined) =
            fibre_populations(&published, &search, &receivers, fibre_bound, abscissa_bound);
        let elapsed = started.elapsed().as_secs_f64();
        println!(
            "surface swept: {examined} (x, T) pairs over {fibre_bound} fibres in {elapsed:.2} s \
             ({:.2e} pairs/s), {} receivers refusing",
            examined as f64 / elapsed.max(1e-9),
            receivers.len()
        );
        let mut ordered: Vec<(&i64, usize)> =
            populations.iter().map(|(f, v)| (f, v.len())).collect();
        ordered.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        println!("\nfibres by realizer population (twelve are forced and carry no information):");
        for (fibre, count) in ordered.iter().take(12) {
            let mark = if **fibre == 2454 {
                "   <- the published rank-17 curve #159"
            } else {
                ""
            };
            println!("   T = {fibre:<6} realizers {count}{mark}");
        }
        // Dump the residual population: for every fibre, the realizers beyond the twelve the
        // family forces. A quadratic section meets each fibre twice, so if the mechanism is what
        // it is claimed to be, these arrive in conjugate pairs whose symmetric functions are low
        // degree in the parameter.
        if arguments.iter().any(|a| a == "--dump") {
            let forced: Vec<i64> = [-1146i64, -2304, -654, 3054, 2880, -1830]
                .iter()
                .flat_map(|a| [*a, *a])
                .collect();
            let _ = forced;
            let mut out = String::new();
            for (fibre, abscissae) in populations.iter() {
                let base: BTreeSet<i64> = [-1146i64, -2304, -654, 3054, 2880, -1830]
                    .iter()
                    .flat_map(|a| [a + fibre, a - fibre])
                    .collect();
                let extra: Vec<i64> = abscissae
                    .iter()
                    .copied()
                    .filter(|x| !base.contains(x))
                    .collect();
                if !extra.is_empty() {
                    out.push_str(&format!("{fibre} {:?}\n", extra));
                }
            }
            std::fs::write("fibre_residual.txt", out).expect("dump");
            println!("\nresidual realizer population written to fibre_residual.txt");
        }
        let place = ordered.iter().position(|(f, _)| **f == 2454);
        match place {
            Some(index) => println!(
                "\nthe published T = 2454 is fibre {} of {} populated, with {} realizers \
                 against a median of {}",
                index + 1,
                ordered.len(),
                populations.get(&2454).map(|v| v.len()).unwrap_or(0),
                ordered[ordered.len() / 2].1
            ),
            None => println!("\nthe published T = 2454 had no realizer in this window"),
        }
        return;
    }

    let deadline = Instant::now() + Duration::from_secs(seconds);
    let mut families = 0u64;
    let mut graded = 0u64;
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
                        let receivers = prepare(&working);
                        let (populations, _) = fibre_populations(
                            &working,
                            &search,
                            &receivers,
                            fibre_bound,
                            abscissa_bound,
                        );
                        // No score selects here. Every fibre the surface gave more realizers than
                        // the family forces is certified exactly, cheaply, on the realizers the
                        // sweep already returned; only what survives that pays for a deep search.
                        // Counting realizers is refused as a selector: measured on the published
                        // family, T = 294 carries thirty and certifies rank 13 while T = 2454
                        // carries sixteen and certifies rank 17.
                        let mut screened: Vec<(usize, i64)> = Vec::new();
                        for (parameter, abscissae) in populations.iter() {
                            if abscissae.len() <= 12 || Instant::now() >= deadline {
                                continue;
                            }
                            let t = BigRational::from_integer(BigInt::from(*parameter));
                            let remainder = working.remainder_at(&t);
                            if remainder.coefficient[4].is_zero() {
                                continue;
                            }
                            let quartic = remainder.integral(&small);
                            let base = remainder.forced_realizers[0].clone();
                            let Some(chart) = QuarticChart::through(&remainder.coefficient, &base)
                            else {
                                continue;
                            };
                            let mut carried = Vec::new();
                            let one = BigInt::from(1);
                            for value in abscissae.iter() {
                                let n = BigInt::from(*value);
                                let Some(root) =
                                    exact_square_root(&homogeneous_value(&quartic, &n, &one))
                                else {
                                    continue;
                                };
                                let x = BigRational::from_integer(n);
                                let y = BigRational::from_integer(root) / quartic.scale.clone();
                                if let Some(point) = chart.carry(&x, &y) {
                                    if chart.curve.contains(&point.0, &point.1) {
                                        carried.push(point);
                                    }
                                }
                            }
                            if carried.len() <= 12 {
                                continue;
                            }
                            let screen =
                                independence_certificate(&chart.curve, &carried, 5, &screen_primes);
                            screened.push((screen.rank_lower_bound, *parameter));
                        }
                        screened.sort_by(|x, y| y.0.cmp(&x.0));
                        for &(_, parameter) in screened.iter().take(keep) {
                            if Instant::now() >= deadline {
                                break 'outer;
                            }
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
                                Some(&weight_ceiling),
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

    println!("\n--- fibration sweep closed ---");
    println!("families off the variety : {families}");
    println!("fibres graded            : {graded}");
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
