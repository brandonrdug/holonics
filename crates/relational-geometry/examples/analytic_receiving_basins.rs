//! Exact analytic source → release → receiving population → circulation.
//! The source laws and supplied seed regions, rather than a known-root table, determine the return.

use relational_geometry::exact::{integer, rat, Rat};
use relational_geometry::exact_analysis::*;
use serde::Serialize;
use std::{cell::Cell, env, fs, time::Instant};

#[derive(Serialize)]
struct RegionReturn {
    initial: ComplexInterval,
    returned: PropagationReturn,
    elapsed_micros: u64,
}

#[derive(Serialize)]
struct ApplicationReturn {
    source: &'static str,
    config: ExactSeriesConfig,
    lambda: Rat,
    discovery_regions: Vec<ComplexInterval>,
    captures: Vec<CaptureCertificate>,
    circulation: Vec<WindingReceipt>,
    regions: Vec<RegionReturn>,
    source_jet_calls: u64,
    elapsed_micros: u64,
}

fn receiver(region: &ComplexInterval) -> ComplexReceiverBox {
    ComplexReceiverBox::new(region.re.clone(), region.im.clone())
}

fn seed(real: Rat, height: Rat) -> ComplexInterval {
    ComplexSquare::new(RatComplex::new(real, height), rat(1, 100_000_000))
        .unwrap()
        .interval()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output = env::args().nth(1).ok_or("supply an output .ron path")?;
    let config = ExactSeriesConfig {
        dyadic_bits: 96,
        euler_maclaurin_start: 24,
        euler_maclaurin_order: 12,
        log_terms: 32,
        exponential_terms: 24,
        trigonometric_terms: 20,
    };
    let lambda = integer(1);
    let clock = Instant::now();
    let calls = Cell::new(0u64);
    let source = |region: &ComplexInterval| {
        calls.set(calls.get() + 1);
        Ok(zeta_evaluate_jet2_with_head(&receiver(region), &config, None)?.jet)
    };
    let discovery_regions: Vec<_> = [14, 21, 25]
        .into_iter()
        .map(|height| seed(rat(1, 2), integer(height)))
        .collect();
    let mut captures = Vec::new();
    let mut circulation = Vec::new();
    for (index, initial) in discovery_regions.iter().enumerate() {
        let mut current = initial.clone();
        for _ in 0..3 {
            current = mean_value_release(source, &current, &lambda, config.dyadic_bits)?;
        }
        // The returned enclosure proposes a proof anchor, not an assumed root.
        // Certification evaluates the actual source anew over its entire neighborhood.
        let certificate = certify_capture(source, &current.midpoint(), &rat(1, 10_000), &lambda)?;
        let square = certificate.square.interval();
        assert!(square.re.lower > integer(0) && square.re.upper < integer(1));
        let winding = eta_boundary_winding(&receiver(&square), &config, 14)?;
        assert_eq!(winding.winding, 1, "independent local divisor receiver");
        println!(
            "capture={index} q_upper_dyadic={:?} center_dyadic={:?} winding={} elapsed_ms={}",
            RatInterval::point(certificate.q.clone()).round_out(12),
            ComplexInterval::point(certificate.square.center.clone()).round_out(24),
            winding.winding,
            clock.elapsed().as_millis()
        );
        captures.push(certificate);
        circulation.push(winding);
    }
    let mut regions = Vec::new();
    for height in [14, 21, 25] {
        for real in [rat(1, 4), rat(1, 2), rat(3, 4)] {
            let initial = seed(real, integer(height));
            let start = Instant::now();
            let returned = propagate_to_capture(
                source,
                initial.clone(),
                &lambda,
                &captures,
                12,
                config.dyadic_bits,
            );
            let elapsed_micros = u64::try_from(start.elapsed().as_micros())?;
            println!(
                "height={height} status={:?} steps={} elapsed_us={elapsed_micros}",
                returned.status, returned.steps
            );
            regions.push(RegionReturn {
                initial,
                returned,
                elapsed_micros,
            });
        }
    }
    // A pole-intersecting box must retain an explicit source-chart obstruction.
    let initial = seed(integer(1), integer(0));
    let start = Instant::now();
    let returned = propagate_to_capture(
        source,
        initial.clone(),
        &lambda,
        &captures,
        12,
        config.dyadic_bits,
    );
    assert!(matches!(
        returned.status,
        PropagationStatus::Obstructed { .. }
    ));
    assert_eq!(returned.remaining, initial);
    regions.push(RegionReturn {
        initial,
        returned,
        elapsed_micros: u64::try_from(start.elapsed().as_micros())?,
    });
    let result = ApplicationReturn {
        source: "Riemann zeta on Re(s)>0 excluding its pole; eta is the independent winding receiver on captured boxes in 0<Re(s)<1",
        config, lambda, discovery_regions, captures, circulation, regions,
        source_jet_calls: calls.get(), elapsed_micros: u64::try_from(clock.elapsed().as_micros())?,
    };
    fs::write(
        &output,
        ron::ser::to_string_pretty(&result, ron::ser::PrettyConfig::default())?,
    )?;
    println!(
        "output={output} source_jet_calls={} total_us={}",
        result.source_jet_calls, result.elapsed_micros
    );
    Ok(())
}
