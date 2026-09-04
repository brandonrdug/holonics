//! Bounded exact probe for one eta receiver box.
//!
//! Usage:
//! `cargo run -p relational-geometry --example holonic_eta_probe -- 14 15`

use std::env;

use num_bigint::BigInt;
use num_rational::BigRational;
use relational_geometry::{
    ComplexReceiverBox, ExactSeriesConfig, RatInterval, eta_boundary_winding, eta_evaluate,
    eta_evaluate_jet, format_rat,
};

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
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
