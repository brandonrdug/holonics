//! Exact arithmetic-monodromy experiment over one growing quintic ecology.
//!
//! The executable supplies an integral quintic and integer chronology. The production
//! `ArithmeticMonodromyLaw` owns normalization, prime founding, finite-field fibers, conditional
//! Galois restriction, formal Euler factors, exact sigma evaluation, and the abstract atlas.
//! A second chronology grades transported-local assembly; future prime sections after the first
//! unique group certificate grade its retained set-valued prediction.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::time::Instant;

use holonic_engine::{
    ArithmeticFiberEvent, ArithmeticMonodromyEvent, ArithmeticMonodromyLaw,
    ArithmeticMonodromyStanding, CausalWorld, EulerReceiverId, EventId, IntegralQuinticProblem,
    QuinticIrreducibility, QuinticProblemId, QuinticTransitiveGroup,
};
use num_bigint::BigInt;

/// **What this driver declares as its horn local-section limit.** `prime_ecology` stopped picking a
/// default on 2026-08-09 (`docs/canon/THE_CONTAMINANT_PROTOCOL.md` §2.5 — *a default is a level the
/// organ picked because the caller was never asked*). It bounds how many affine
/// integer-polynomial torsors one horn-resolution event may retain; past it the event refuses by
/// name rather than sampling.
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

const PROBLEM: QuinticProblemId = QuinticProblemId(17);
const RECEIVER: EulerReceiverId = EulerReceiverId(23);
const PROBLEM_EVENT: EventId = EventId(1_000_000);
const RECEIVER_EVENT: EventId = EventId(2_000_000);
const EVENT_LIMIT: u64 = 1_000_000;

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let limit = arguments
        .first()
        .map_or(Ok(97_u64), |value| value.parse::<u64>())?;
    if !(11..EVENT_LIMIT).contains(&limit) {
        return Err(format!("integer limit must satisfy 11 <= limit < {EVENT_LIMIT}").into());
    }
    let coefficients = arguments
        .get(1)
        .map(|value| parse_coefficients(value))
        .transpose()?
        .unwrap_or_else(default_a5_coefficients);
    let problem =
        IntegralQuinticProblem::new(PROBLEM, "arithmetic-monodromy-subject", coefficients)?;

    let start = Instant::now();
    let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, HORN_LOCAL_SECTION_LIMIT)?;
    let standing =
        ArithmeticMonodromyStanding::with_horn_local_section_limit(1, HORN_LOCAL_SECTION_LIMIT)?;
    let mut world = CausalWorld::new(law, standing);
    world.receive(&ArithmeticMonodromyEvent::InheritQuintic {
        event: PROBLEM_EVENT,
        problem: problem.clone(),
    })?;
    world.receive(&ArithmeticMonodromyEvent::OpenEulerReceiver {
        event: RECEIVER_EVENT,
        id: RECEIVER,
        problem: PROBLEM,
        sigma: 2,
    })?;

    let mut first_unique_at = None;
    let mut admitted_after_certificate = None::<BTreeSet<Vec<u32>>>;
    let mut held_out_unramified = 0_u64;
    let mut held_out_residuals = Vec::new();
    for value in 2..=limit {
        let receipt = world.receive(&ArithmeticMonodromyEvent::AdmitInteger(
            ArithmeticFiberEvent {
                event: EventId(value),
                value,
            },
        ))?;
        let radiation = &receipt.radiation[0];
        for delta in &radiation.galois_deltas {
            if first_unique_at.is_none() && delta.unique_group_after.is_some() {
                first_unique_at = Some((value, delta.prime, delta.unique_group_after));
                admitted_after_certificate = Some(
                    world.standing().problems()[&PROBLEM]
                        .galois
                        .admitted_future_cycle_types()?,
                );
                continue;
            }
            if let Some(admitted) = &admitted_after_certificate {
                for section in radiation
                    .transported_sections
                    .iter()
                    .filter(|section| section.problem == PROBLEM)
                {
                    if let Some(cycle_type) = &section.cycle_type {
                        held_out_unramified += 1;
                        if !admitted.contains(cycle_type) {
                            held_out_residuals.push((section.prime, cycle_type.clone()));
                        }
                    }
                }
            }
        }
    }
    world.standing().validate()?;

    let alternate_law =
        ArithmeticMonodromyLaw::with_horn_local_section_limit(1, HORN_LOCAL_SECTION_LIMIT)?;
    let alternate_standing =
        ArithmeticMonodromyStanding::with_horn_local_section_limit(1, HORN_LOCAL_SECTION_LIMIT)?;
    let mut alternate = CausalWorld::new(alternate_law, alternate_standing);
    admit_through(&mut alternate, limit)?;
    alternate.receive(&ArithmeticMonodromyEvent::InheritQuintic {
        event: PROBLEM_EVENT,
        problem,
    })?;
    alternate.receive(&ArithmeticMonodromyEvent::OpenEulerReceiver {
        event: RECEIVER_EVENT,
        id: RECEIVER,
        problem: PROBLEM,
        sigma: 2,
    })?;
    alternate.standing().validate()?;

    let standing = world.standing();
    let quintic = &standing.problems()[&PROBLEM];
    let receiver = &standing.euler_receivers()[&RECEIVER];
    let atlas = standing.atlas_receipt(PROBLEM)?;
    let chronology_geometry_equal =
        standing.geometry_receipt() == alternate.standing().geometry_receipt();
    let lineage_reused_exactly = receiver.local_sections.iter().all(|(prime, local)| {
        quintic.prime_sections[prime].source_events == local.source_events
            && quintic.prime_sections[prime].euler_denominator.as_ref()
                == Some(&local.denominator_polynomial)
    });
    let cycle_histogram = quintic
        .prime_sections
        .values()
        .filter_map(|section| section.cycle_type.clone())
        .fold(BTreeMap::<Vec<u32>, u64>::new(), |mut counts, cycle| {
            *counts.entry(cycle).or_default() += 1;
            counts
        });
    let factor_work = standing.prime_ecology().fibers().values().fold(
        (0_u64, 0_u64, 0_u64, 0_u64),
        |(gcd, columns, eliminations, shifts), fiber| {
            (
                gcd + fiber.work.gcd_divisions,
                columns + fiber.work.frobenius_columns,
                eliminations + fiber.work.row_eliminations,
                shifts + fiber.work.berlekamp_shifts,
            )
        },
    );
    let irreducibility_prime = match &quintic.galois.irreducibility {
        QuinticIrreducibility::Open => None,
        QuinticIrreducibility::CertifiedByPrime { prime, .. } => Some(*prime),
    };
    let unique_group = quintic.galois.unique_certified_group();
    let group_is_nonsolvable = unique_group.is_some_and(|group| !group.solvable_by_radicals());
    let certified_group_cycle_constraints_hold = unique_group
        != Some(QuinticTransitiveGroup::Alternating5)
        || quintic
            .prime_sections
            .values()
            .filter_map(|section| section.permutation_is_even)
            .all(|even| even);
    let glued_transport_cells = atlas
        .transport_cells
        .iter()
        .filter(|cell| cell.glued)
        .count();

    println!("schema=holonic-engine.arithmetic-monodromy-experiment.v1");
    println!("integer_limit={limit}");
    println!("inherited_coefficients={:?}", quintic.problem.coefficients);
    println!(
        "normalized_coefficients={:?}",
        quintic.normalized.coefficients
    );
    println!("root_scale={}", quintic.normalized.root_scale);
    println!("discriminant={}", quintic.normalized.discriminant);
    println!(
        "discriminant_square_root={:?}",
        quintic.normalized.discriminant_square_root
    );
    println!(
        "founded_primes={}",
        standing.prime_ecology().arithmetic().prime_cells().len()
    );
    println!("prime_sections={}", quintic.prime_sections.len());
    println!(
        "unramified_power_basis_sections={}",
        receiver.local_sections.len()
    );
    println!(
        "open_polynomial_discriminant_places={:?}",
        receiver.open_places.keys().collect::<Vec<_>>()
    );
    println!("cycle_histogram={cycle_histogram:?}");
    println!("irreducibility_certificate_prime={irreducibility_prime:?}");
    println!(
        "transitive_candidates={:?}",
        quintic.galois.transitive_candidates
    );
    println!("unique_certified_group={unique_group:?}");
    println!("unique_group_nonsolvable_by_radicals={group_is_nonsolvable}");
    println!("first_unique_certificate={first_unique_at:?}");
    println!(
        "admitted_future_cycle_types={:?}",
        admitted_after_certificate
    );
    println!("held_out_unramified_sections={held_out_unramified}");
    println!("held_out_cycle_residuals={held_out_residuals:?}");
    println!("certified_group_cycle_constraints_hold={certified_group_cycle_constraints_hold}");
    println!("euler_sigma={}", receiver.sigma);
    println!("euler_product_numerator={}", receiver.exact_product.numer());
    println!(
        "euler_product_denominator={}",
        receiver.exact_product.denom()
    );
    println!("factor_work_gcd_divisions={}", factor_work.0);
    println!("factor_work_frobenius_columns={}", factor_work.1);
    println!("factor_work_row_eliminations={}", factor_work.2);
    println!("factor_work_berlekamp_shifts={}", factor_work.3);
    println!("atlas_prime_charts={}", atlas.prime_charts.len());
    println!("atlas_transport_cells={}", atlas.transport_cells.len());
    println!("atlas_glued_transport_cells={glued_transport_cells}");
    println!(
        "atlas_cross_prime_root_sheet_gluing={:?}",
        atlas.cross_prime_root_sheet_gluing
    );
    println!("lineage_reused_exactly={lineage_reused_exactly}");
    println!("chronology_geometry_equal={chronology_geometry_equal}");
    println!("elapsed_millis={}", start.elapsed().as_millis());

    if !chronology_geometry_equal
        || !lineage_reused_exactly
        || !held_out_residuals.is_empty()
        || !certified_group_cycle_constraints_hold
    {
        return Err("arithmetic-monodromy acceptance residual is nonzero".into());
    }
    Ok(())
}

fn admit_through(
    world: &mut CausalWorld<ArithmeticMonodromyLaw>,
    through: u64,
) -> Result<(), Box<dyn Error>> {
    for value in 2..=through {
        world.receive(&ArithmeticMonodromyEvent::AdmitInteger(
            ArithmeticFiberEvent {
                event: EventId(value),
                value,
            },
        ))?;
    }
    Ok(())
}

fn parse_coefficients(value: &str) -> Result<Vec<BigInt>, Box<dyn Error>> {
    let coefficients = value
        .split(',')
        .map(str::parse::<BigInt>)
        .collect::<Result<Vec<_>, _>>()?;
    if coefficients.len() != 6 {
        return Err("coefficient argument must contain a0,a1,a2,a3,a4,a5".into());
    }
    Ok(coefficients)
}

fn default_a5_coefficients() -> Vec<BigInt> {
    // Twice x^5 - x^4 - 11x^3 + x^2 + 12x - 4. The scalar keeps the
    // inherited presentation nonmonic while preserving its totally real A5 roots.
    [-8_i64, 24, 2, -22, -2, 2]
        .into_iter()
        .map(BigInt::from)
        .collect()
}
