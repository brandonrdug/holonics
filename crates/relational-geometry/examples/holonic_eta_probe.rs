//! Bounded exact probe for one eta receiver box, and the **chain** underneath it.
//!
//! Usage:
//! `cargo run -p relational-geometry --example holonic_eta_probe -- 14 15`
//! `cargo run -p relational-geometry --example holonic_eta_probe -- 14 15 chain [grain]`
//!
//! The `chain` mode returns what the evaluator forms and discards: every head
//! term as an **amplitude and a turn** rather than as their product, every
//! Euler--Maclaurin correction as a **crossing** with its Bernoulli weight and
//! its hand, and Borwein's independent chain beside it as a second frame.
//!
//! Nothing here is a float. `grain` declares how coarse an **exact dyadic**
//! enclosure to print; widening is `round_out`, which is exact, so a coarser
//! grain is a coarser true enclosure and never a rounded decimal.

use std::env;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, ExactSeriesConfig, RatInterval, eta_borwein_chain,
    eta_boundary_winding, eta_chain_decomposition, eta_evaluate, eta_evaluate_jet, format_rat,
};

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn overlaps(left: &RatInterval, right: &RatInterval) -> bool {
    left.lower <= right.upper && right.lower <= left.upper
}

fn show(value: &ComplexInterval, grain: u32) -> String {
    let coarse = value.round_out(grain);
    format!("re={} im={}", coarse.re, coarse.im)
}

/// An exact rational, shown as the exact dyadic enclosure at a declared grain.
/// This is a widening, never a decimal: the true value lies inside what is printed.
fn grain_text(value: &BigRational, grain: u32) -> String {
    RatInterval::point(value.clone())
        .round_out(grain)
        .to_string()
}

/// The integer `k` with `2^-(k+1) < value <= 2^-k` — how many octaves below one the
/// value sits. An exact integer reading of a magnitude, with no decimal face and no
/// display truncation to floor it.
fn octave(value: &BigRational) -> i64 {
    if value.is_zero() {
        return i64::MAX;
    }
    let one = BigRational::from_integer(BigInt::from(1));
    let two = BigRational::from_integer(BigInt::from(2));
    let half = one.clone() / two.clone();
    let mut scaled = value.clone();
    let mut octaves: i64 = 0;
    while scaled > one {
        scaled /= &two;
        octaves -= 1;
    }
    while scaled <= half {
        scaled *= &two;
        octaves += 1;
    }
    octaves
}

/// `(17 + 12*sqrt 2)^k` as an exact pair of integers in the ring adjoining `sqrt 2`.
/// `17 + 12*sqrt 2 = (3 + sqrt 8)^2 = (1 + sqrt 2)^4`, and the ring is closed under
/// multiplication, so the power never leaves the integers.
fn unit_power(power: u32) -> (BigInt, BigInt) {
    let (mut a, mut b) = (BigInt::from(1), BigInt::from(0));
    for _ in 0..power {
        let next_a = BigInt::from(17) * &a + BigInt::from(24) * &b;
        let next_b = BigInt::from(12) * &a + BigInt::from(17) * &b;
        a = next_a;
        b = next_b;
    }
    (a, b)
}

/// The largest `m` with `2^m <= a + b*sqrt 2`, decided by integer comparison alone:
/// `2^m <= a + b*sqrt 2` iff `2^m <= a`, or else `(2^m - a)^2 <= 2 b^2`.
fn surd_octaves(a: &BigInt, b: &BigInt) -> i64 {
    let admits = |m: i64| -> bool {
        let threshold = BigInt::from(1) << (m as u32);
        if threshold <= *a {
            return true;
        }
        let excess = &threshold - a;
        &excess * &excess <= BigInt::from(2) * b * b
    };
    let mut m: i64 = 0;
    while admits(m + 1) {
        m += 1;
    }
    m
}

fn main() {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let tau_lower = arguments
        .first()
        .map(|value| value.parse::<i64>().expect("integer lower tau"))
        .unwrap_or(14);
    let tau_upper = arguments
        .get(1)
        .map(|value| value.parse::<i64>().expect("integer upper tau"))
        .unwrap_or(15);
    let receiver = ComplexReceiverBox::new(
        RatInterval::new(
            BigRational::new(BigInt::from(2), BigInt::from(5)),
            BigRational::new(BigInt::from(3), BigInt::from(5)),
        ),
        RatInterval::new(integer(tau_lower), integer(tau_upper)),
    );
    let config = ExactSeriesConfig {
        dyadic_bits: 96,
        euler_maclaurin_start: 12,
        euler_maclaurin_order: 10,
        log_terms: 28,
        exponential_terms: 18,
        trigonometric_terms: 16,
    };
    if arguments.get(2).is_some_and(|value| value == "point") {
        let point = ComplexReceiverBox::point(
            BigRational::new(BigInt::from(1), BigInt::from(2)),
            integer(tau_lower),
        );
        let result = eta_evaluate(&point, &config).expect("point evaluation");
        println!("point {} value={}", tau_lower, result.value);
        return;
    }
    if arguments.get(2).is_some_and(|value| value == "small") {
        let small = ComplexReceiverBox::new(
            RatInterval::point(BigRational::new(BigInt::from(1), BigInt::from(2))),
            RatInterval::new(
                integer(tau_lower),
                integer(tau_lower) + BigRational::new(BigInt::from(1), BigInt::from(256)),
            ),
        );
        let result = eta_evaluate(&small, &config).expect("small segment evaluation");
        println!(
            "small tau={} value={} origin={}",
            small.tau,
            result.value,
            result.value.contains_origin()
        );
        return;
    }
    if arguments.get(2).is_some_and(|value| value == "jet") {
        let side = ComplexReceiverBox::new(
            RatInterval::point(BigRational::new(BigInt::from(2), BigInt::from(5))),
            RatInterval::new(integer(tau_lower), integer(tau_upper)),
        );
        let result = eta_evaluate_jet(&side, &config).expect("jet evaluation");
        println!(
            "jet receiver sigma={} tau={} derivative={} l1={}",
            side.sigma,
            side.tau,
            result.derivative,
            format_rat(&result.derivative.l1_upper())
        );
        return;
    }
    if arguments.get(2).is_some_and(|value| value == "chain") {
        let grain = arguments
            .get(3)
            .map(|value| value.parse::<u32>().expect("integer grain"))
            .unwrap_or(20);
        chain_probe(tau_lower, &config, grain);
        return;
    }
    let receipt = eta_boundary_winding(&receiver, &config, 14)
        .expect("the declared boundary must be certified");

    println!(
        "receiver sigma={} tau={} winding={} segments={} ray={}",
        receiver.sigma,
        receiver.tau,
        receipt.winding,
        receipt.segments.len(),
        receipt.ray_parameter
    );
    for (index, segment) in receipt.segments.iter().enumerate() {
        println!(
            "{index}: ({},{}) -> ({},{}) depth={} image={}",
            format_rat(&segment.start.re),
            format_rat(&segment.start.im),
            format_rat(&segment.end.re),
            format_rat(&segment.end.im),
            segment.depth,
            segment.image
        );
    }
}

fn chain_probe(tau: i64, config: &ExactSeriesConfig, grain: u32) {
    let point = ComplexReceiverBox::point(
        BigRational::new(BigInt::from(1), BigInt::from(2)),
        integer(tau),
    );
    let chain = eta_chain_decomposition(&point, config).expect("the chain decomposition");

    println!("RECEIVER  sigma={} tau={}", point.sigma, point.tau);
    println!("GRAIN     every enclosure below is exact and printed at 2^-{grain}\n");

    println!("1. THE HEAD CHAIN — each term an amplitude and a turn, not their product");
    println!("   n^(-s) = exp(-sigma*log n) * cis(-tau*log n)\n");
    println!(
        "   {:>3}  {:<12} {:<26} {:<26}",
        "n", "address", "amplitude", "turn (additive chart)"
    );
    for term in &chain.head {
        let address = if term.address.is_empty() {
            "1 (empty)".to_string()
        } else {
            term.address
                .iter()
                .map(|valuation| {
                    if valuation.exponent == 1 {
                        format!("{}", valuation.prime)
                    } else {
                        format!("{}^{}", valuation.prime, valuation.exponent)
                    }
                })
                .collect::<Vec<_>>()
                .join("*")
        };
        println!(
            "   {:>3}  {:<12} {:<26} {:<26}",
            term.base,
            address,
            term.amplitude.round_out(grain).to_string(),
            term.turn.round_out(grain).to_string()
        );
    }

    println!("\n2. THE CROSSINGS — Bernoulli weight, hand, and the shift-orbit product");
    println!("   term = B_2k/(2k)! * (s)_(2k-1) * N^(-s) / N^(2k-1)\n");
    println!(
        "   {:>5}  {:>4}  {:<16} {:<24} {:>4}",
        "order", "2k", "B_2k", "B_2k/(2k)!", "hand"
    );
    let mut even_orders = 0;
    for crossing in &chain.crossings {
        if crossing.crossing_order % 2 == 0 {
            even_orders += 1;
        }
        println!(
            "   {:>5}  {:>4}  {:<16} {:<24} {:>4}",
            crossing.crossing_order,
            crossing.bernoulli_index,
            format_rat(&crossing.bernoulli),
            format_rat(&crossing.coefficient),
            if crossing.hand >= 0 { "+" } else { "-" }
        );
    }
    println!(
        "\n   PARITY  crossings of even order: {even_orders} of {} — the odd-index",
        chain.crossings.len()
    );
    println!("           Bernoulli numbers vanish, so only odd crossing orders exist.");
    println!("           That decides which terms exist before any magnitude is computed.");

    println!("\n3. THE CHART TRANSITION — what summation pays to become integration");
    println!(
        "   integral term  N^(1-s)/(s-1)   {}",
        show(&chain.integral_term, grain)
    );
    println!(
        "   boundary half  N^(-s)/2        {}",
        show(&chain.boundary_half, grain)
    );
    println!(
        "   remainder radius (certified)   {}",
        format_rat(&chain.remainder_radius)
    );

    println!("\n4. TWO FRAMES ON ONE VALUE");
    println!(
        "   zeta                           {}",
        show(&chain.zeta, grain)
    );
    println!(
        "   alternating rebase 1 - 2^(1-s) {}",
        show(&chain.alternating_factor, grain)
    );
    println!(
        "   eta  (Euler-Maclaurin)         {}",
        show(&chain.eta, grain)
    );

    println!("\n   Borwein's depth sweep. His bound carries 1/|Gamma(s)|, which grows with the");
    println!("   height, so the depth the second frame needs is a function of tau — and this");
    println!("   body owns no Gamma, so the crossover is measured rather than predicted.\n");
    let mut crossover = None;
    let mut marks = String::new();
    for depth in 12u32..=40 {
        let borwein = eta_borwein_chain(&point, depth, config).expect("the Borwein chain");
        let agrees = overlaps(&borwein.value.re, &chain.eta.re)
            && overlaps(&borwein.value.im, &chain.eta.im);
        if agrees && crossover.is_none() {
            crossover = Some(depth);
        }
        marks.push(if agrees { 'o' } else { '.' });
    }
    println!("   depth      12{}40", " ".repeat(24));
    println!("   overlap    {marks}      ('.' disagree, 'o' agree)");

    println!("\n   THE DECAY RATE, and it is checked with no square root anywhere.");
    println!("   Borwein's remainder decays like (3 + sqrt 8)^-n, and 3 + sqrt 8 = (1 + sqrt 2)^2");
    println!("   is the square of the fundamental unit. It is the root of x^2 - 6x + 1, so the");
    println!("   claim 'the rate is that unit' is the exact rational test r^2 - 6r + 1 = 0.\n");
    println!("   Measured against ITSELF — successive Borwein values, not against the other");
    println!("   frame. Comparing to Euler--Maclaurin floors the reading at that frame's own");
    println!("   error; |B_(n+1) - B_n| decays at the same rate and needs no true value.\n");
    println!("   The successive difference is COMPLEX and it rotates, so its real part passes");
    println!("   through zero and is not a decay. The squared magnitude re^2 + im^2 is exact,");
    println!("   rotation-blind, and needs no square root. Its ratio must approach (3+sqrt 8)^2,");
    println!("   which is the root of x^2 - 34x + 1 — so that residual is the whole test.\n");
    let mut previous_value: Option<(BigRational, BigRational)> = None;
    let mut previous_gap: Option<BigRational> = None;
    let mut window: Vec<(u32, i64)> = Vec::new();
    println!(
        "   {:>4}  {:>8}  {:<26}  {}",
        "n", "octave", "ratio r of squared gaps", "r^2 - 34r + 1"
    );
    for depth in 6u32..=32 {
        let borwein = eta_borwein_chain(&point, depth, config).expect("the Borwein chain");
        let middle = borwein.value.midpoint();
        let Some((last_re, last_im)) =
            previous_value.replace((middle.re.clone(), middle.im.clone()))
        else {
            continue;
        };
        let delta_re = middle.re - last_re;
        let delta_im = middle.im - last_im;
        let gap = &delta_re * &delta_re + &delta_im * &delta_im;
        let (ratio_text, residual_text) = match &previous_gap {
            Some(last) if !gap.is_zero() => {
                let ratio = last / &gap;
                let residual = &ratio * &ratio
                    - BigRational::from_integer(BigInt::from(34)) * &ratio
                    + BigRational::from_integer(BigInt::from(1));
                (grain_text(&ratio, 12), grain_text(&residual, 6))
            }
            _ => ("—".to_string(), "—".to_string()),
        };
        let octaves = octave(&gap);
        window.push((depth, octaves));
        println!(
            "   {:>4}  {:>8}  {:<26}  {}",
            depth, octaves, ratio_text, residual_text
        );
        previous_gap = Some(gap);
    }

    println!("\n   THE CLOSING COMPARISON, and no square root is taken to make it.");
    println!("   The early steps are pre-asymptotic — they gain one octave each — so the window");
    println!("   is DECLARED rather than fitted, and both halves are reported.\n");
    let halfway = window.len() / 2;
    for (label, slice) in [
        ("whole sweep     ", &window[..]),
        ("declared tail   ", &window[halfway..]),
    ] {
        let (Some(first), Some(last)) = (slice.first(), slice.last()) else {
            continue;
        };
        let steps = last.0 - first.0;
        let measured = last.1 - first.1;
        let (a, b) = unit_power(steps);
        let predicted = surd_octaves(&a, &b);
        println!(
            "   {label} n={:>2}..{:<2} ({steps:>2} steps)   measured {measured:>3} octaves   \
             (17+12*sqrt2)^{steps} sits in octave {predicted:>3}   difference {}",
            first.0,
            last.0,
            (measured - predicted).abs()
        );
    }
    println!(
        "\n   The prediction is an exact integer decided by (2^m - a)^2 vs 2b^2, and the ring"
    );
    println!("   adjoining sqrt 2 is closed under multiplication so the power never leaves ℤ.");
    println!("   Read the difference above; it is the verdict, and this line does not assert one.");
    match crossover {
        Some(depth) => println!(
            "\n   CROSSOVER at n={depth} for tau={tau}. Below it the frames genuinely disagree;\n   \
             the disagreement is the Gamma factor this body cannot compute, made visible."
        ),
        None => println!("\n   NO CROSSOVER up to n=40 — the frames never met at this height."),
    }

    println!("\n5. THE TRAVERSAL — the complex parts, as exact ratios");
    let box_receiver = ComplexReceiverBox::new(
        RatInterval::new(
            BigRational::new(BigInt::from(2), BigInt::from(5)),
            BigRational::new(BigInt::from(3), BigInt::from(5)),
        ),
        RatInterval::new(
            BigRational::new(BigInt::from(8 * tau + 1), BigInt::from(8)),
            BigRational::new(BigInt::from(4 * tau + 1), BigInt::from(4)),
        ),
    );
    match eta_boundary_winding(&box_receiver, config, 10) {
        Ok(receipt) => {
            println!(
                "   box sigma={} tau={} winding={} segments={}\n",
                box_receiver.sigma,
                box_receiver.tau,
                receipt.winding,
                receipt.segments.len()
            );
            for (index, segment) in receipt.segments.iter().enumerate().take(8) {
                println!(
                    "   [{index}] corner ({}, {})",
                    format_rat(&segment.start.re),
                    format_rat(&segment.start.im)
                );
                println!("        eta there  {}", show(&segment.start_value, grain));
            }
            if receipt.segments.len() > 8 {
                println!(
                    "   ... {} further segments, all retained in the receipt",
                    receipt.segments.len() - 8
                );
            }
        }
        Err(error) => println!("   winding refused: {error}"),
    }
}
