//! Bounded instrument for recurrent prime-horn filler families.
//!
//! The application supplies four prime occurrences, three inherited
//! quadratics, and five open-horn supports. It supplies no local continuation
//! section or integer-polynomial filler. The production `PrimeEcologyLaw`
//! derives every finite-field stratum, symbolic constraint intersection, CRT
//! family, caused cell, and lineage relation reported below.

use std::collections::BTreeMap;
use std::error::Error;

use holonic_engine::{
    ArithmeticFiberEvent, CausalWorld, EventId, HornFillerBranch, IntegerPolynomialProbe,
    MonicPolynomialConstraintFamily, PolynomialProbeId, PrimeEcologyEvent, PrimeEcologyLaw,
    PrimeEcologyStanding, PrimeHornStatus, PrimePhaseSource,
};
use num_bigint::BigInt;

/// **What this driver declares as its horn local-section limit.** `prime_ecology` stopped picking a
/// default on 2026-08-09 (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5 — *a default is a level the
/// organ picked because the caller was never asked*). It bounds how many affine
/// integer-polynomial torsors one horn-resolution event may retain; past it the event refuses by
/// name rather than sampling.
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

const TRIANGLES: [[u64; 3]; 4] = [[2, 3, 5], [2, 3, 7], [2, 5, 7], [3, 5, 7]];

fn probes() -> Result<Vec<(EventId, IntegerPolynomialProbe)>, Box<dyn Error>> {
    [(6_u64, 100_u64), (10, 101), (14, 102)]
        .into_iter()
        .map(|(linear, event)| {
            Ok((
                EventId(event),
                IntegerPolynomialProbe::new(
                    PolynomialProbeId(linear),
                    format!("quadratic-pairing[{linear}]"),
                    vec![BigInt::from(0), BigInt::from(linear), BigInt::from(1)],
                )?,
            ))
        })
        .collect()
}

fn main() -> Result<(), Box<dyn Error>> {
    let law = PrimeEcologyLaw::with_horn_local_section_limit(3, HORN_LOCAL_SECTION_LIMIT)?;
    let standing = PrimeEcologyStanding::with_horn_local_section_limit(3, HORN_LOCAL_SECTION_LIMIT)?;
    let mut world = CausalWorld::new(law, standing);
    for value in 2..=7 {
        world.receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
            event: EventId(value - 1),
            value,
        }))?;
    }
    for (event, probe) in probes()? {
        world.receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })?;
    }

    let triangle_supports = TRIANGLES.map(Vec::from);
    let pair_cells_before = world
        .standing()
        .phase_cells()
        .values()
        .filter(|cell| cell.grade == 1)
        .count();
    let open_triangles_before = triangle_supports
        .iter()
        .filter(|support| {
            world
                .standing()
                .horns()
                .get(*support)
                .is_some_and(|horn| horn.status == PrimeHornStatus::Open)
        })
        .count();
    let tetrahedron = vec![2, 3, 5, 7];
    let tetrahedron_existed_before_faces =
        world.standing().phase_cells().contains_key(&tetrahedron);

    let mut face_branch_counts = BTreeMap::new();
    for (offset, support) in triangle_supports.iter().enumerate() {
        let receipt = world.receive(&PrimeEcologyEvent::ResolveHorn {
            event: EventId(200 + u64::try_from(offset)?),
            support: support.clone(),
        })?;
        let filler = receipt.radiation[0]
            .induced_filler_space
            .as_ref()
            .ok_or("triangle resolution emitted no filler space")?;
        face_branch_counts.insert(support.clone(), filler.branches.len());
    }

    let tetrahedron_was_open = world
        .standing()
        .horns()
        .get(&tetrahedron)
        .is_some_and(|horn| horn.status == PrimeHornStatus::Open);
    let boundary_is_entirely_induced = triangle_supports.iter().all(|support| {
        world.standing().phase_cells()[support]
            .witness_features
            .iter()
            .all(|feature| matches!(&feature.source, PrimePhaseSource::HornFillerBranch(_)))
    });

    let receipt = world.receive(&PrimeEcologyEvent::ResolveHorn {
        event: EventId(204),
        support: tetrahedron.clone(),
    })?;
    let filler = receipt.radiation[0]
        .induced_filler_space
        .as_ref()
        .ok_or("tetrahedral resolution emitted no filler space")?;
    let mut homologous = BTreeMap::<MonicPolynomialConstraintFamily, Vec<&HornFillerBranch>>::new();
    for branch in &filler.branches {
        homologous
            .entry(branch.constraint_family()?)
            .or_default()
            .push(branch);
    }
    let homologous_paths_are_exact = homologous.values().all(|branches| {
        branches.len() == 2
            && branches[0].torsors(HORN_LOCAL_SECTION_LIMIT).is_ok_and(|left| {
                branches[1]
                    .torsors(HORN_LOCAL_SECTION_LIMIT)
                    .is_ok_and(|right| left == right)
            })
    });
    let family_receipts = homologous
        .iter()
        .map(|(family, branches)| {
            (
                family.fixed_sections.keys().copied().collect::<Vec<_>>(),
                family.local_strata.keys().copied().collect::<Vec<_>>(),
                family.section_count,
                branches
                    .iter()
                    .map(|branch| {
                        (
                            branch.source_face.clone(),
                            branch.missing_prime,
                            branch.source_feature.source.clone(),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    world.standing().validate()?;
    println!("schema\tholonic-engine.prime-ecology-recombination-instrument.v1");
    println!("receivers\t{:?}", [2, 3, 5, 7]);
    println!("inherited_quadratics\t{:?}", [6, 10, 14]);
    println!("pair_cells_before_resolution\t{pair_cells_before}");
    println!("open_triangles_before_resolution\t{open_triangles_before}");
    println!("tetrahedron_existed_before_faces\t{tetrahedron_existed_before_faces}");
    println!("triangle_filler_branch_counts\t{face_branch_counts:?}");
    println!("tetrahedron_was_open\t{tetrahedron_was_open}");
    println!("tetrahedron_boundary_entirely_induced\t{boundary_is_entirely_induced}");
    println!("tetrahedral_causal_branches\t{}", filler.branches.len());
    println!("chronology_free_families\t{}", homologous.len());
    println!("homologous_paths_are_exact\t{homologous_paths_are_exact}");
    println!("family_receipts\t{family_receipts:?}");
    println!(
        "tetrahedron_filled\t{}",
        world.standing().phase_cells().contains_key(&tetrahedron)
    );
    println!(
        "causal_f_vector\t{:?}",
        world.standing().arithmetic().incidence().f_vector()
    );
    Ok(())
}
