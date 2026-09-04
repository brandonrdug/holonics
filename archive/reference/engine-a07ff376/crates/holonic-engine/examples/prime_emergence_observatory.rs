//! Exact observatory for prime recognition, obstruction, recurrence, and
//! finite-place Zeta receiver geometry.
//!
//! The application supplies only consecutive integer occurrences.  It does
//! not supply prime labels, factor witnesses, recognition depths, valuation
//! vectors, prime-power events, or Zeta masses.  Those are enacted or derived
//! by the production `ArithmeticFiberLaw`.  The larger polynomial/horn prime
//! ecology composes this same mouth, but is deliberately not mounted when the
//! experiment supplies no polynomial material.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use holonic_engine::{
    ArithmeticFiberEvent, ArithmeticFiberLaw, ArithmeticFiberStanding, CausalWorld, EventId,
    PrimePowerCurrentEvent, PrimeRecognitionClosure,
};
use num_bigint::BigInt;
use relational_geometry::Rat;

fn main() -> Result<(), Box<dyn Error>> {
    let limit = std::env::args()
        .nth(1)
        .map_or(Ok(256_u64), |value| value.parse::<u64>())?;
    if limit < 2 {
        return Err("prime emergence observatory requires a limit of at least two".into());
    }

    let mut world = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
    let mut prime_power_events = BTreeMap::<u64, PrimePowerCurrentEvent>::new();

    for value in 2..=limit {
        let receipt = world.receive(&ArithmeticFiberEvent {
            event: EventId(value - 1),
            value,
        })?;
        let arithmetic = &receipt.radiation[0];
        if let Some(current_event) = &arithmetic.prime_power_event {
            prime_power_events.insert(value, current_event.clone());
        }
    }

    world.standing().validate()?;
    let arithmetic = world.standing();
    let selected_primes = arithmetic
        .prime_cells()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let zeta = arithmetic.zeta_receiver_measure(2, &selected_primes)?;

    let mut prime_count = 0_u64;
    let mut composite_count = 0_u64;
    let mut obstruction_count = 0_u64;
    let mut open_fiber_sections = 0_u64;
    let mut lower_bound_work = 0_u64;
    let mut upper_bound_work = 0_u64;
    let mut closure_depth_distribution = BTreeMap::<u64, u64>::new();
    let mut maximum_depth = 0_u64;
    let mut maximum_depth_candidates = Vec::new();

    for trace in arithmetic.recognitions().values() {
        match &trace.closure {
            PrimeRecognitionClosure::Irreducible { .. } => prime_count += 1,
            PrimeRecognitionClosure::Composite { .. } => composite_count += 1,
        }
        obstruction_count += u64::from(trace.irreducibility_obstruction.is_some());
        open_fiber_sections += trace.open_fiber_count();
        lower_bound_work += trace.bounds.distinguishing_probe_lower_bound;
        upper_bound_work += trace.bounds.certificate_probe_upper_bound;
        *closure_depth_distribution
            .entry(trace.bounds.certificate_probe_upper_bound)
            .or_default() += 1;
        match trace
            .bounds
            .certificate_probe_upper_bound
            .cmp(&maximum_depth)
        {
            std::cmp::Ordering::Greater => {
                maximum_depth = trace.bounds.certificate_probe_upper_bound;
                maximum_depth_candidates = vec![trace.candidate];
            }
            std::cmp::Ordering::Equal => maximum_depth_candidates.push(trace.candidate),
            std::cmp::Ordering::Less => {}
        }
    }

    println!("schema\tholonic-engine.prime-emergence-observatory.v1");
    println!("source_material\tconsecutive-integer-occurrences-only");
    println!("integer_standing\t{}", arithmetic.value);
    println!("candidate_population\t{}", arithmetic.recognitions().len());
    println!("founded_prime_population\t{prime_count}");
    println!("composite_population\t{composite_count}");
    println!("irreducibility_obstruction_fronts\t{obstruction_count}");
    println!("open_continuation_fiber_sections\t{open_fiber_sections}");
    println!("recognition_lower_bound_work\t{lower_bound_work}");
    println!("recognition_certificate_work\t{upper_bound_work}");
    println!(
        "all_ordered_receiver_bounds_close\t{}",
        lower_bound_work == upper_bound_work
            && arithmetic.recognitions().values().all(|trace| {
                trace.open_fiber_count() == trace.bounds.distinguishing_probe_lower_bound
                    && trace.bounds.distinguishing_probe_lower_bound
                        == trace.bounds.certificate_probe_upper_bound
            })
    );
    println!("closure_depth_distribution\t{closure_depth_distribution:?}");
    println!("maximum_closure_depth\t{maximum_depth}");
    println!("maximum_depth_candidates\t{maximum_depth_candidates:?}");
    let maximum_depth_irreducibles = maximum_depth_candidates
        .iter()
        .filter(|candidate| {
            matches!(
                &arithmetic.recognitions()[&**candidate].closure,
                PrimeRecognitionClosure::Irreducible { .. }
            )
        })
        .count();
    let maximum_depth_composite_fronts = maximum_depth_candidates
        .iter()
        .filter_map(
            |candidate| match &arithmetic.recognitions()[candidate].closure {
                PrimeRecognitionClosure::Composite { witness } => {
                    Some((*candidate, witness.prime_axis, witness.cofactor))
                }
                PrimeRecognitionClosure::Irreducible { .. } => None,
            },
        )
        .collect::<Vec<_>>();
    println!("maximum_depth_irreducibles\t{maximum_depth_irreducibles}");
    println!("maximum_depth_composite_fronts\t{maximum_depth_composite_fronts:?}");
    println!("prime_power_event_population\t{}", prime_power_events.len());
    println!(
        "chebyshev_log_coefficients\t{:?}",
        arithmetic.prime_power_current().log_coefficients
    );
    println!(
        "chebyshev_product_lcm\t{}",
        arithmetic.prime_power_current().chebyshev_product
    );
    println!(
        "formal_chebyshev_departure\tlog({})-{}",
        arithmetic.prime_power_current().chebyshev_product,
        arithmetic
            .prime_power_current()
            .formal_departure()
            .smooth_coordinate
    );
    println!("zeta_receiver_sigma\t{}", zeta.sigma);
    println!("zeta_selected_places\t{:?}", zeta.selected_primes);
    println!(
        "zeta_coprime_cell_mass\t{}",
        format_rat(&zeta.coprime_cell_mass)
    );
    println!(
        "zeta_valuation_return_mass\t{}",
        format_rat(&zeta.valuation_return_mass)
    );
    println!(
        "zeta_cut_return_closes\t{}",
        &zeta.coprime_cell_mass * &zeta.valuation_return_mass == Rat::from_integer(1.into())
    );
    println!(
        "receiver_population_ratio_prime_to_all\t{}",
        format_rat(&Rat::new(
            BigInt::from(prime_count),
            BigInt::from(prime_count + composite_count),
        ))
    );

    println!(
        "trace_columns\tcandidate\tclosure\tfactor_horizon\tlower_bound\tupper_bound\topen_fibers\tobstruction_front\tvaluation\tprime_power_current"
    );
    for (candidate, trace) in arithmetic.recognitions() {
        let closure = match &trace.closure {
            PrimeRecognitionClosure::Irreducible { .. } => "irreducible".to_owned(),
            PrimeRecognitionClosure::Composite { witness } => {
                format!("composite:{}*{}", witness.prime_axis, witness.cofactor)
            }
        };
        let obstruction = trace.irreducibility_obstruction.as_ref().map_or_else(
            || "-".to_owned(),
            |front| {
                format!(
                    "depth{}:{}*{}",
                    front.depth, front.witness.prime_axis, front.witness.cofactor
                )
            },
        );
        let occurrence = &arithmetic.occurrences()[candidate];
        let valuation = occurrence
            .valuation
            .iter()
            .map(|factor| format!("{}^{}", factor.prime, factor.exponent))
            .collect::<Vec<_>>()
            .join("*");
        let current_event = prime_power_events.get(candidate).map_or_else(
            || "-".to_owned(),
            |event| {
                format!(
                    "log({}):coefficient{}",
                    event.prime, event.log_coefficient_after
                )
            },
        );
        println!(
            "trace\t{candidate}\t{closure}\t{}\t{}\t{}\t{}\t{obstruction}\t{valuation}\t{current_event}",
            trace.bounds.factor_horizon_axis_count,
            trace.bounds.distinguishing_probe_lower_bound,
            trace.bounds.certificate_probe_upper_bound,
            trace.open_fiber_count(),
        );
    }

    println!("standing_exactly_validated\ttrue");
    Ok(())
}

fn format_rat(value: &Rat) -> String {
    format!("{}/{}", value.numer(), value.denom())
}
