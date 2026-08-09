//! Bounded reporting instrument for the topology-forming prime ecology.
//!
//! This executable supplies only integer occurrences and inherited
//! cyclotomic probes. Prime founding, factorization, Frobenius transport,
//! feature intersection, horn formation, coefficientwise CRT continuation,
//! and horn filling remain owned by `PrimeEcologyLaw`.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use holonic_engine::{
    ArithmeticFiberEvent, CausalWorld, EventId, IntegerPolynomialProbe, PolynomialProbeId,
    PrimeEcologyEvent, PrimeEcologyLaw, PrimeEcologyStanding, PrimeHornStatus,
};
use num_bigint::BigInt;
use num_traits::One;

/// **What this driver declares as its horn local-section limit.** `prime_ecology` stopped picking a
/// default on 2026-08-09 (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5 — *a default is a level the
/// organ picked because the caller was never asked*). It bounds how many affine
/// integer-polynomial torsors one horn-resolution event may retain; past it the event refuses by
/// name rather than sampling.
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

const PROBE_EVENT_BASE: u64 = 1_000_000;

fn main() -> Result<(), Box<dyn Error>> {
    let limit = std::env::args()
        .nth(1)
        .map_or(Ok(31_u64), |value| value.parse::<u64>())?;
    if !(5..PROBE_EVENT_BASE).contains(&limit) {
        return Err(format!("prime limit must satisfy 5 <= limit < {PROBE_EVENT_BASE}").into());
    }

    let probes = probes()?;
    let law = PrimeEcologyLaw::with_horn_local_section_limit(2, HORN_LOCAL_SECTION_LIMIT)?;
    let standing = PrimeEcologyStanding::with_horn_local_section_limit(2, HORN_LOCAL_SECTION_LIMIT)?;
    let mut world = CausalWorld::new(law, standing);
    admit_integers(&mut world, 2, 5)?;

    for (event, probe) in probes.iter().cloned() {
        world.receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })?;
    }
    let triangle = vec![2, 3, 5];
    let triangle_was_open = world
        .standing()
        .horns()
        .get(&triangle)
        .is_some_and(|horn| horn.status == PrimeHornStatus::Open);
    let open_horns_before_filler = world.standing().open_horns().count();

    let filler_receipt = world.receive(&PrimeEcologyEvent::ResolveHorn {
        event: EventId(PROBE_EVENT_BASE + 3),
        support: triangle.clone(),
    })?;
    let filler_space = filler_receipt.radiation[0]
        .induced_filler_space
        .as_ref()
        .ok_or("horn resolution emitted no filler space")?;
    let triangle_filled_in_event = filler_receipt.radiation[0]
        .filled_horns
        .iter()
        .any(|horn| horn.support == triangle);
    let branch_torsor_counts = filler_space
        .branches
        .iter()
        .map(|branch| (branch.source_face.clone(), branch.torsor_count()))
        .collect::<BTreeMap<_, _>>();
    let quadratic_branch = filler_space
        .branches
        .iter()
        .find(|branch| branch.source_face == vec![2, 5])
        .ok_or("the degree-two continuation branch is absent")?;
    let inherited_bridge_is_member =
        quadratic_branch.contains(&[BigInt::from(11), BigInt::one(), BigInt::one()]);
    let selected = BTreeSet::from([2, 3, 5]);
    let selected_before_enlargement = world.standing().geometry_receipt_for(&selected);
    admit_integers(&mut world, 6, limit)?;
    let selected_after_enlargement = world.standing().geometry_receipt_for(&selected);
    let seven_refinement = (limit >= 7)
        .then(|| {
            world
                .standing()
                .refine_filler_branch_at_prime(quadratic_branch.id, 7)
        })
        .transpose()?;

    let presentation = world.standing().compare_presentation(
        3,
        PolynomialProbeId(2),
        vec![
            BigInt::from(4),
            BigInt::from(-2),
            BigInt::from(7),
            BigInt::from(-5),
            BigInt::from(4),
        ],
    )?;

    let alternate_law = PrimeEcologyLaw::with_horn_local_section_limit(2, HORN_LOCAL_SECTION_LIMIT)?;
    let alternate_standing = PrimeEcologyStanding::with_horn_local_section_limit(2, HORN_LOCAL_SECTION_LIMIT)?;
    let mut alternate = CausalWorld::new(alternate_law, alternate_standing);
    for (event, probe) in probes {
        alternate.receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })?;
    }
    admit_integers(&mut alternate, 2, limit)?;
    alternate.receive(&PrimeEcologyEvent::ResolveHorn {
        event: EventId(PROBE_EVENT_BASE + 3),
        support: triangle.clone(),
    })?;

    world.standing().validate()?;
    alternate.standing().validate()?;
    let phase_f_vector = world.standing().phase_cells().values().fold(
        BTreeMap::<u32, usize>::new(),
        |mut counts, cell| {
            *counts.entry(cell.grade).or_default() += 1;
            counts
        },
    );
    let factor_work = world.standing().fibers().values().fold(
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
    let phi3_signatures = world
        .standing()
        .fibers()
        .iter()
        .filter_map(|((prime, probe), fiber)| {
            (*probe == PolynomialProbeId(1))
                .then_some((*prime, fiber.signature.factor_phases.clone()))
        })
        .collect::<BTreeMap<_, _>>();

    println!("schema\tholonic-engine.prime-ecology-calibration-instrument.v2");
    println!("integer_standing\t{}", world.standing().arithmetic().value);
    println!(
        "founded_primes\t{}",
        world.standing().arithmetic().prime_cells().len()
    );
    println!("inherited_probes\t{}", world.standing().probes().len());
    println!(
        "induced_filler_spaces\t{}",
        world.standing().filler_spaces().len()
    );
    println!("polynomial_fibers\t{}", world.standing().fibers().len());
    println!("phase_f_vector\t{phase_f_vector:?}");
    println!(
        "multiplicative_and_phase_f_vector\t{:?}",
        world.standing().arithmetic().incidence().f_vector()
    );
    println!("triangle_235_was_open\t{triangle_was_open}");
    println!("open_horns_before_filler\t{open_horns_before_filler}");
    println!("triangle_235_filled_in_resolution_event\t{triangle_filled_in_event}");
    println!("filler_branch_torsor_counts\t{branch_torsor_counts:?}");
    println!("quadratic_bridge_is_family_member\t{inherited_bridge_is_member}");
    if let Some(refinement) = seven_refinement {
        println!(
            "quadratic_branch_prime_7_covering\t{}",
            refinement.children_per_parent
        );
        println!(
            "quadratic_branch_prime_7_strata\t{:?}",
            refinement
                .strata
                .iter()
                .map(|stratum| (
                    stratum.measure.section_count,
                    stratum.measure.numerator,
                    stratum.measure.denominator,
                ))
                .collect::<Vec<_>>()
        );
    }
    println!(
        "triangle_235_filled_now\t{}",
        world.standing().phase_cells().contains_key(&vec![2, 3, 5])
    );
    println!(
        "selected_geometry_survives_enlargement\t{}",
        selected_before_enlargement == selected_after_enlargement
    );
    println!(
        "probe_prime_choreography_same_geometry\t{}",
        world.standing().geometry_receipt() == alternate.standing().geometry_receipt()
    );
    println!(
        "alternate_choreography_has_triangle_horn_history\t{}",
        alternate.standing().horns().contains_key(&vec![2, 3, 5])
    );
    println!(
        "presentation_reduction_same\t{}",
        presentation.same_reduction
    );
    println!(
        "presentation_signature_same\t{}",
        presentation.same_signature
    );
    println!("phi3_phase_signatures\t{phi3_signatures:?}");
    println!(
        "factor_work_gcd_columns_eliminations_shifts\t{:?}",
        factor_work
    );
    println!("standing_exactly_validated\ttrue");
    Ok(())
}

fn probes() -> Result<Vec<(EventId, IntegerPolynomialProbe)>, Box<dyn Error>> {
    Ok(vec![
        (
            EventId(PROBE_EVENT_BASE),
            IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(1), 3)?,
        ),
        (
            EventId(PROBE_EVENT_BASE + 1),
            IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(2), 5)?,
        ),
        (
            EventId(PROBE_EVENT_BASE + 2),
            IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(3), 7)?,
        ),
    ])
}

fn admit_integers(
    world: &mut CausalWorld<PrimeEcologyLaw>,
    first: u64,
    last: u64,
) -> Result<(), Box<dyn Error>> {
    for value in first..=last {
        world.receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
            event: EventId(value - 1),
            value,
        }))?;
    }
    Ok(())
}
