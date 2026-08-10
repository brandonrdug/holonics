//! How far up the degree ladder the Tschirnhaus organ still returns, and what stops it.
//!
//! `the_degree_is_a_rung` drives degrees two through seven. This driver asks the next question and
//! only that question: **where does the ladder stop returning, and is the stop a typed refusal or a
//! degradation?** It is a scale measurement, not a mathematical deed — every claim it makes is
//! about the organ's own reach, and the mathematics it exercises is already owned by
//! `quintic_chart.rs` and `arithmetic_monodromy.rs`.
//!
//! Degrees are read off the declared inputs. Nothing here pins a maximum: the ladder is walked
//! until the organ refuses, and the refusal is printed verbatim.
//!
//! Apparatus testimony only — timings are the caller's frame and decide nothing.

use std::error::Error;
use std::time::Instant;

use holonic_engine::arithmetic_monodromy::{IntegralQuinticProblem, QuinticProblemId};
use holonic_engine::quintic_chart::{QuinticChart, read_quintic_charts, tschirnhaus_cost};
use num_bigint::BigInt;

/// Declared by this caller, matching `the_degree_is_a_rung` so the two are comparable.
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;
const PRIME_LIMIT: u64 = 97;

/// The declared ladder. Every entry is a real integer polynomial; the family is the two shapes the
/// existing driver already uses, extended in degree only, so that degree is the single variable.
fn ladder() -> Vec<(String, Vec<i64>)> {
    let mut declared = Vec::new();
    for degree in [5usize, 6, 7, 8, 9, 10, 12, 14, 16, 20, 24, 32] {
        // x^n - x - 1, the classical irreducible family (Selmer): coefficient-first.
        let mut trinomial = vec![-1i64, -1];
        trinomial.resize(degree + 1, 0);
        trinomial[degree] = 1;
        declared.push((format!("trinomial x^{degree} - x - 1"), trinomial));

        // A dense polynomial: (x+1)^n written out, so every coefficient is nonzero and large.
        let mut binomial_expansion = vec![0i64; degree + 1];
        let mut coefficient: i128 = 1;
        for index in 0..=degree {
            binomial_expansion[index] = coefficient as i64;
            coefficient = coefficient * (degree - index) as i128 / (index as i128 + 1);
        }
        declared.push((format!("dense (x+1)^{degree}"), binomial_expansion));
    }
    declared
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("THE DEGREE LADDER IS PUSHED");
    println!("=============================");
    println!();
    println!("The organ is `quintic_chart::read_quintic_charts`, driven past the degrees any");
    println!("committed driver reaches. prime limit {PRIME_LIMIT}, horn limit {HORN_LOCAL_SECTION_LIMIT}.");
    println!();

    println!("--- THE BEZOUT COST LAW, WHICH IS INDEPENDENT OF THE SOURCE DEGREE ---");
    for transform_degree in 1..=10usize {
        println!("  {}", tschirnhaus_cost(transform_degree).written());
    }
    println!();

    println!("--- THE LADDER ---");
    println!(
        "{:<26} {:>4} {:>10} {:>9} {:>9} {:>9} {:>7}  {}",
        "input", "deg", "wall_ms", "depressed", "principal", "bring", "obstr", "radical verdict"
    );

    let mut refusals: Vec<(String, String)> = Vec::new();
    for (index, (name, coefficients)) in ladder().into_iter().enumerate() {
        let degree = coefficients.len() - 1;
        let problem = match IntegralQuinticProblem::new(
            QuinticProblemId(index as u64 + 1),
            Box::leak(name.clone().into_boxed_str()),
            coefficients.iter().map(|value| BigInt::from(*value)).collect(),
        ) {
            Ok(problem) => problem,
            Err(error) => {
                println!("{name:<26} {degree:>4}   REFUSED AT CONSTRUCTION: {error}");
                refusals.push((name, format!("{error}")));
                continue;
            }
        };

        let start = Instant::now();
        let atlas = match read_quintic_charts(&problem, PRIME_LIMIT, HORN_LOCAL_SECTION_LIMIT) {
            Ok(atlas) => atlas,
            Err(error) => {
                println!(
                    "{name:<26} {degree:>4} {:>10}   REFUSED: {error}",
                    start.elapsed().as_millis()
                );
                refusals.push((name, format!("{error}")));
                continue;
            }
        };
        let elapsed = start.elapsed().as_millis();

        let outcome_word = |chart: QuinticChart| -> &'static str {
            let outcome = atlas
                .outcomes()
                .into_iter()
                .find(|(candidate, _)| *candidate == chart)
                .map(|(_, outcome)| outcome);
            match outcome {
                Some(outcome) => match outcome.transport() {
                    Some(transport) => {
                        if transport.certificate.holds() {
                            "RETURNS"
                        } else {
                            "UNCERTIFIED"
                        }
                    }
                    None => "refused",
                },
                None => "-",
            }
        };

        println!(
            "{name:<26} {degree:>4} {elapsed:>10} {:>9} {:>9} {:>9} {:>7}  {:?}",
            outcome_word(QuinticChart::Depressed),
            outcome_word(QuinticChart::Principal),
            outcome_word(QuinticChart::Bring),
            atlas.obstructions.len(),
            atlas.radical.verdict,
        );

        for obstruction in &atlas.obstructions {
            println!("        obstruction  {obstruction:?}");
        }
    }

    println!();
    println!("--- REFUSALS, VERBATIM ---");
    if refusals.is_empty() {
        println!("  none: the organ returned at every declared degree.");
    } else {
        for (name, error) in &refusals {
            println!("  {name}: {error}");
        }
    }
    Ok(())
}
