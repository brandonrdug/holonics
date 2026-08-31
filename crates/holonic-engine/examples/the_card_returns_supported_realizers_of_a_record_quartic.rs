//! The card searches a record curve's quartic model for supported realizers.
//!
//! The control is exterior and it is sharp: leaderboard curve #159 was published with seventeen
//! independent points. Eleven are forced by the family; five more were found by an integral-`x`
//! search and one at a denominator near `3·10^11`. This driver rebuilds the family from its six
//! published values, hands the quartic to the card, and must recover the eleven forced realizers
//! **and** the five searched ones without being told any of them. Anything beyond those is a
//! realizer the published search did not report.
//!
//! Run with `PATH=/opt/cuda/bin:$PATH`.

use holonic_engine::{
    CudaRealizerReceiverFamily as ReceiverFamily, QuarticChart, RealizerSextuple,
    ResidentRealizerSearch, exact_square_root, homogeneous_value, independence_certificate,
    minimalise, primes_upto,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::BTreeSet;
use std::env;
use std::time::Instant;

fn rational(values: [i64; 6]) -> [BigRational; 6] {
    values.map(|v| BigRational::from_integer(BigInt::from(v)))
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    let integral_bound: i64 = arguments
        .iter()
        .position(|a| a == "--integral-bound")
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(1_000_000);
    let denominator_bound: i64 = arguments
        .iter()
        .position(|a| a == "--denominator-bound")
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    let numerator_bound: i64 = arguments
        .iter()
        .position(|a| a == "--numerator-bound")
        .and_then(|i| arguments.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(1_000_000);

    let sextuple: Vec<i64> = arguments
        .iter()
        .position(|a| a == "--sextuple")
        .and_then(|i| arguments.get(i + 1))
        .map(|v| v.split(',').filter_map(|t| t.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![-1146, -2304, -654, 3054, 2880, -1830]);
    let parameter_text = arguments
        .iter()
        .position(|a| a == "--parameter")
        .and_then(|i| arguments.get(i + 1))
        .cloned()
        .unwrap_or_else(|| "2454".to_owned());
    let (pn, pd) = parameter_text
        .split_once('/')
        .map(|(a, b)| (a.to_owned(), b.to_owned()))
        .unwrap_or((parameter_text.clone(), "1".to_owned()));

    let small = primes_upto(100_000);
    let mut six = [0i64; 6];
    six.copy_from_slice(&sextuple[..6]);
    let family = RealizerSextuple::found_after_centring(rational(six))
        .expect("the sextuple must lie on the variety");
    let parameter = BigRational::new(
        BigInt::parse_bytes(pn.as_bytes(), 10).expect("numerator"),
        BigInt::parse_bytes(pd.as_bytes(), 10).expect("denominator"),
    );
    let remainder = family.remainder_at(&parameter);
    let quartic = remainder.integral(&small);
    let (c4, c6) = quartic.invariants();
    let minimal = minimalise(&c4, &c6, &small);

    println!("realizer family rebuilt");
    println!("  sextuple      {sextuple:?},  T = {parameter}");
    println!("  quartic       {:?}", quartic.coefficient);
    println!("  minimal c4    {}", minimal.c4);
    println!("  minimal c6    {}", minimal.c6);
    println!("  a-invariants  {:?}", minimal.a_invariants);
    println!("  rescale u     {}", minimal.rescale);

    let forced: BTreeSet<(i64, i64)> = remainder
        .forced_realizers
        .iter()
        .map(|(x, _)| {
            (
                x.numer().try_into().unwrap_or(i64::MAX),
                x.denom().try_into().unwrap_or(1),
            )
        })
        .collect();
    // The five the published search reported at d = 1, held back from the card and used only to
    // grade what comes out.
    let published_searched: BTreeSet<i64> =
        [5880, 14154, 17386, -24392, 211716].into_iter().collect();

    let receiver_primes: Vec<u64> = primes_upto(200)
        .into_iter()
        .filter(|&p| p >= 3)
        .take(40)
        .collect();
    let receivers = ReceiverFamily::declare(&quartic, &receiver_primes);
    println!(
        "\ndeclared {} prime receivers (3 ..= {})",
        receivers.receiver_count(),
        receivers.primes().last().copied().unwrap_or(0)
    );

    let search = match ResidentRealizerSearch::mount() {
        Ok(search) => search,
        Err(error) => {
            eprintln!("the card refused the mount: {error}");
            std::process::exit(1);
        }
    };

    let mut admitted: Vec<(BigInt, BigInt, BigInt)> = Vec::new();
    // `x = n/d` is one realizer however the pair is written, so the pair is reduced before the
    // exact test. The first draft skipped this and reported `-48784/2` as new when it is the
    // published `-24392`: a duplicate presented as a discovery, which is the defect this whole
    // pipeline exists to refuse.
    fn reduce(n: i64, d: i64) -> (i64, i64) {
        let (mut a, mut b) = (n.unsigned_abs(), d.unsigned_abs());
        while b != 0 {
            let t = a % b;
            a = b;
            b = t;
        }
        let g = a.max(1) as i64;
        (n / g, d / g)
    }
    let record = |n: i64, d: i64, admitted: &mut Vec<(BigInt, BigInt, BigInt)>| {
        let (n, d) = reduce(n, d);
        let bn = BigInt::from(n);
        let bd = BigInt::from(d);
        let value = homogeneous_value(&quartic, &bn, &bd);
        if let Some(root) = exact_square_root(&value) {
            admitted.push((bn, bd, root));
        }
    };

    // ---- the integral face, d = 1 ----
    let started = Instant::now();
    let count = 2 * integral_bound + 1;
    let integral = search
        .sweep_integral(&receivers, -integral_bound, count, 1 << 20)
        .expect("the integral sweep returns");
    let integral_elapsed = started.elapsed();
    for &(n, d) in integral.survivors.iter() {
        record(n, d, &mut admitted);
    }
    println!(
        "\nintegral sweep  |n| <= {integral_bound}: {} examined, {} survived the receivers, \
         {:.3} s",
        integral.pairs_examined,
        integral.survivors.len(),
        integral_elapsed.as_secs_f64()
    );

    // ---- the rational face ----
    if denominator_bound > 1 {
        let started = Instant::now();
        let mut survivors = 0usize;
        let mut examined = 0u128;
        let mut low = 2i64;
        while low <= denominator_bound {
            let span = (denominator_bound - low + 1).min(1024);
            let sweep = search
                .sweep_rational(
                    &receivers,
                    low,
                    span,
                    -numerator_bound,
                    2 * numerator_bound + 1,
                    1 << 20,
                )
                .expect("the rational sweep returns");
            survivors += sweep.survivors.len();
            examined += sweep.pairs_examined;
            for &(n, d) in sweep.survivors.iter() {
                record(n, d, &mut admitted);
            }
            low += span;
        }
        println!(
            "rational sweep  2 <= d <= {denominator_bound}, |n| <= {numerator_bound}: \
             {examined} examined, {survivors} survived, {:.3} s",
            started.elapsed().as_secs_f64()
        );
    }

    // ---- grade: carry every admitted realizer onto the model and certify the rank ----
    let mut seen: BTreeSet<(i64, i64)> = BTreeSet::new();
    let mut distinct: Vec<(BigRational, BigRational)> = Vec::new();
    let mut novel = 0usize;
    for (n, d, y) in admitted.iter() {
        let key = (n.try_into().unwrap_or(i64::MAX), d.try_into().unwrap_or(1));
        if !seen.insert(key) {
            continue;
        }
        if !forced.contains(&key) && !(key.1 == 1 && published_searched.contains(&key.0)) {
            novel += 1;
        }
        let x = BigRational::new(n.clone(), d.clone());
        // the ordinate on the *integral* quartic; the chart divides it back out
        let yq = BigRational::new(y.clone(), d.clone() * d.clone()) / quartic.scale.clone();
        distinct.push((x, yq));
    }
    println!(
        "\ndistinct realizers on the quartic: {} ({} outside the published seventeen)",
        distinct.len(),
        novel
    );

    let base = remainder.forced_realizers[0].clone();
    let chart = QuarticChart::through(&remainder.coefficient, &base).expect("a chart exists");
    let mut carried = Vec::new();
    let mut off_curve = 0usize;
    for (x, y) in distinct.iter() {
        match chart.carry(x, y) {
            Some(point) if chart.curve.contains(&point.0, &point.1) => carried.push(point),
            Some(_) => off_curve += 1,
            None => {}
        }
    }
    println!(
        "carried onto the minimal model: {} realizers ({off_curve} failed the on-curve check)",
        carried.len()
    );
    let started = Instant::now();
    let receivers = primes_upto(6000);
    let certificate = independence_certificate(&chart.curve, &carried, 5, &receivers);
    println!(
        "\nEXACT RANK LOWER BOUND = {}  (torsion prime {}, {} prime receivers, torsion free: {}) \
         in {:.2} s",
        certificate.rank_lower_bound,
        certificate.torsion_prime,
        certificate.receivers.len(),
        certificate.torsion_free,
        started.elapsed().as_secs_f64()
    );
    println!("no height pairing was formed; no floating-point operation entered the certificate.");
}
