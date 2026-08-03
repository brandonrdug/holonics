//! Bounded research instrument for the arithmetic-fiber production laws.
//!
//! This executable does not own prime founding, root counting, grammar
//! discovery, or diffusion.  It only supplies an integer chronology and
//! reports the exact receipts returned by `holonic-engine`.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use holonic_engine::{
    ArithmeticFiberEvent, ArithmeticFiberLaw, ArithmeticFiberStanding, CausalWorld, EventId,
    ExactSheafCochain, ExactSheafDiffusionLaw, SheafDiffusionEvent, calibrate_quadratic_transport,
    residue_transport_sheaf, residue_triangle_obstructions,
};
use num_bigint::BigInt;
use relational_geometry::{format_rat, integer};

fn main() -> Result<(), Box<dyn Error>> {
    let mut arguments = std::env::args().skip(1);
    let training_ceiling = parse_or(arguments.next(), 97)?;
    let heldout_ceiling = parse_or(arguments.next(), 251)?;
    let grammar_bound = parse_or(arguments.next(), 16)?;
    if arguments.next().is_some() {
        return Err("usage: prime_fiber_calibration [training] [heldout] [grammar]".into());
    }

    let mut world = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
    for value in 2..=heldout_ceiling {
        world.receive(&ArithmeticFiberEvent {
            event: EventId(value - 1),
            value,
        })?;
    }
    let standing = world.standing();
    let calibration =
        calibrate_quadratic_transport(standing, training_ceiling, heldout_ceiling, grammar_bound)?;

    let mut selected = BTreeSet::new();
    for prime in standing
        .prime_cells()
        .keys()
        .copied()
        .filter(|prime| *prime > 2)
    {
        if selected.len() == 5 {
            break;
        }
        let admissible = selected.iter().all(|other| {
            prime
                .checked_mul(*other)
                .is_some_and(|product| product <= standing.value)
                && calibration
                    .transport
                    .receive(prime, *other)
                    .ok()
                    .and_then(|read| read.predicted_hand)
                    .is_some()
        });
        if admissible {
            selected.insert(prime);
        }
    }
    let obstructions = residue_triangle_obstructions(&calibration.transport, &selected)?;
    let negative_cycles = obstructions
        .iter()
        .filter(|receipt| receipt.cycle_holonomy == -1)
        .count();
    let positive_cycles = obstructions.len() - negative_cycles;
    let sheaf = residue_transport_sheaf(standing, &calibration.transport, &selected)?;
    let capacities = sheaf
        .complex()
        .cells()
        .iter()
        .filter(|(_, body)| body.grade == 0)
        .map(|(cell, _)| {
            let selected_cell = selected
                .iter()
                .any(|prime| standing.prime_cells()[prime] == *cell);
            (
                *cell,
                if selected_cell {
                    vec![integer(1)]
                } else {
                    Vec::new()
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let law = ExactSheafDiffusionLaw::new(sheaf.clone(), 0, capacities)?;
    let mut content = ExactSheafCochain::zero(&sheaf, 0);
    let first_prime = selected
        .iter()
        .next()
        .copied()
        .ok_or("the selected prime ecology is empty")?;
    content
        .values
        .get_mut(&standing.prime_cells()[&first_prime])
        .ok_or("selected prime has no cochain stalk")?[0] = integer(1);
    let initial = law.initial_standing(content)?;
    let (after, diffusion) = law.enact(
        &initial,
        &SheafDiffusionEvent {
            interval: integer(1),
            source: BTreeMap::new(),
        },
    )?;

    let translated_controls = calibration
        .heldout
        .iter()
        .map(|grade| {
            standing
                .quadratic_fiber(
                    grade.pair.lower_prime,
                    BigInt::from(grade.pair.upper_prime) + BigInt::from(3) * grade.pair.lower_prime,
                )
                .map(|translated| translated.roots == grade.pair.lower_receives_upper.roots)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let unit_controls = calibration
        .heldout
        .iter()
        .map(|grade| {
            grade
                .pair
                .lower_receives_upper
                .unit_scale(2)
                .map(|receipt| receipt.character_preserved)
        })
        .collect::<Result<Vec<_>, _>>()?;

    println!("schema\tholonic-engine.prime-fiber-calibration-instrument.v1");
    println!("integer_standing\t{}", standing.value);
    println!("founded_primes\t{}", standing.prime_cells().len());
    println!("incidence_f_vector\t{:?}", standing.incidence().f_vector());
    println!("training_pairs\t{}", calibration.training.len());
    println!("heldout_pairs\t{}", calibration.heldout.len());
    println!("grammar_bound\t{}", grammar_bound);
    println!("selected_modulus\t{}", calibration.transport.modulus);
    println!("learned_buckets\t{:?}", calibration.transport.hands);
    println!(
        "heldout_buckets_complete\t{}",
        calibration.all_heldout_buckets_received
    );
    println!(
        "heldout_residuals_zero\t{}",
        calibration.all_heldout_residuals_zero
    );
    println!(
        "translation_controls_zero\t{}",
        translated_controls.iter().all(|passed| *passed)
    );
    println!(
        "unit_isomorphism_controls_zero\t{}",
        unit_controls.iter().all(|passed| *passed)
    );
    println!("selected_primes\t{:?}", selected);
    println!("positive_triangle_holonomies\t{positive_cycles}");
    println!("negative_triangle_holonomies\t{negative_cycles}");
    println!(
        "grade_zero_harmonic_dimension\t{}",
        diffusion.certificate.harmonic_dimension
    );
    println!(
        "diffusion_energy_before\t{}",
        format_rat(&diffusion.stored_energy_before)
    );
    println!(
        "diffusion_energy_after\t{}",
        format_rat(&diffusion.stored_energy_after)
    );
    println!(
        "diffusion_energy_departed\t{}",
        format_rat(&diffusion.energy_departed)
    );
    println!(
        "diffusion_balance_zero\t{}",
        diffusion
            .balance_residual
            .values
            .values()
            .flatten()
            .all(num_traits::Zero::is_zero)
    );
    let selected_after = selected
        .iter()
        .map(|prime| {
            (
                *prime,
                after.content.values[&standing.prime_cells()[prime]][0].clone(),
            )
        })
        .collect::<Vec<_>>();
    println!(
        "selected_content_after\t{:?}",
        selected_after
            .iter()
            .map(|(prime, value)| (*prime, format_rat(value)))
            .collect::<Vec<_>>()
    );
    Ok(())
}

fn parse_or(value: Option<String>, default: u64) -> Result<u64, Box<dyn Error>> {
    value.map_or(Ok(default), |value| {
        value
            .parse::<u64>()
            .map_err(|error| Box::new(error) as Box<dyn Error>)
    })
}
