//! The certified reading's checks that need engine owners: the arithmetic-fibre pair law and the
//! production rigidity consumer. The reading and its own laws are tested with their owner,
//! `holonic_core::prime_image_algebra`.

use num_bigint::BigInt;
use relational_geometry::Rat;

/// The environment variable that turns the consumer measurement on, and the coordinate extents.
const CONSUMER_ENV: &str = "HOLONICS_PRIME_IMAGE_CONSUMER";

/// The lattice geometry the consumer reading is built from — the same places, jitter and aperture
/// as `holonic_core::prime_image_algebra`'s fixture Jacobian, so the two measurements read one
/// material.
const SPACING: i64 = 3_800;
const APERTURE_SQUARED: i64 = 8_000 * 8_000;
const GRAIN: i64 = 1_000;

/// A serpentine lattice path of `points` occurrences with a deterministic sub-lattice jitter.
///
/// Consecutive occurrences are neighbours and the path stays compact, so a point carries on the
/// order of eighteen contacts inside the aperture — the density of a folded chain rather than of a
/// free walk. The jitter is far below the spacing: it makes the placement generic without changing
/// which pairs fall inside the aperture.
fn lattice_places(points: usize) -> Vec<[i64; 3]> {
    let side = (1i64..)
        .find(|side| side * side * side >= points as i64)
        .unwrap_or(1);
    (0..points as i64)
        .map(|index| {
            let z = index / (side * side);
            let within = index % (side * side);
            let y = if z % 2 == 0 {
                within / side
            } else {
                side - 1 - within / side
            };
            let x = if (within / side) % 2 == 0 {
                within % side
            } else {
                side - 1 - within % side
            };
            [
                x * SPACING + (index * 137) % 401 - 200,
                y * SPACING + (index * 223) % 401 - 200,
                z * SPACING + (index * 331) % 401 - 200,
            ]
        })
        .collect()
}

/// The exact squared separation of two lattice places, in the lattice's own integer units.
fn separation(left: &[i64; 3], right: &[i64; 3]) -> i64 {
    (0..3)
        .map(|axis| {
            let difference = left[axis] - right[axis];
            difference * difference
        })
        .sum()
}

/// **The hoisted lift agrees with the pair law it specialises.** The certified reading lifts its
/// images with a hoisted CRT accumulator (`holonic_core::prime_image_algebra`); the arithmetic
/// fibre owns the pair law `chinese_remainder_pair`. Folding the same images through the pair law
/// returns the same residues and modulus, and the lift reconstructs every original value.
#[test]
fn the_hoisted_lift_agrees_with_the_pair_law_it_specialises() {
    use crate::arithmetic_fiber::{ExactCongruence, chinese_remainder_pair};

    let values: Vec<u64> = vec![17, 0, 4_000_000_001, 999];
    let (moduli, residues, modulus, reconstructed) =
        holonic_core::prime_image_algebra::hoisted_lift_probe(&values, 3).expect("three charts");
    assert_eq!(moduli.len(), 3);
    let mut combined: Option<Vec<ExactCongruence>> = None;
    for chart in &moduli {
        let image: Vec<u64> = values.iter().map(|value| value % chart).collect();
        combined = Some(match combined {
            None => image
                .iter()
                .map(|residue| {
                    ExactCongruence::new(BigInt::from(*residue), BigInt::from(*chart))
                        .expect("a congruence")
                })
                .collect(),
            Some(standing) => standing
                .into_iter()
                .zip(&image)
                .map(|(left, residue)| {
                    chinese_remainder_pair(
                        left,
                        ExactCongruence::new(BigInt::from(*residue), BigInt::from(*chart))
                            .expect("a congruence"),
                    )
                    .expect("coprime moduli")
                    .combined
                })
                .collect(),
        });
    }

    let pairwise = combined.expect("at least one round");
    for (at, congruence) in pairwise.iter().enumerate() {
        assert_eq!(
            residues[at], congruence.residue,
            "the hoisted lift is the pair law with the Bezout coefficient taken out of the loop"
        );
        assert_eq!(modulus, congruence.modulus);
    }

    // And the lift is faithful: every original value reconstructs once the window admits it.
    let reconstructed = reconstructed.expect("the window admits these");
    for (at, value) in values.iter().enumerate() {
        assert_eq!(reconstructed[at], Rat::from_integer(BigInt::from(*value)));
    }
}

/// **Synthetic lattice material read through the production consumer.**
///
/// `rigidity_receiver::rigidity_reading` is one of the two consumers Issue #50 measures, and this
/// owner edits nothing in it: the Jacobian below is built through that module's own
/// `ExactConfiguration` and `ConstraintEdge` constructors, from the same lattice places
/// `holonic_core::prime_image_algebra`'s fixture Jacobian uses, and the reading is taken by the public function unchanged.
///
/// The consumer shares the rank/kernel return and separately reads the cokernel; its
/// rank–nullity, cokernel and Maxwell checks constrain those returned dimensions. These
/// checks do not make the synthetic source equivalent to an unreturned measured input.
///
/// Off by default; taken with `HOLONICS_PRIME_IMAGE_CONSUMER=324,612 cargo test --release
/// -p holonic-engine --lib prime_image_algebra::tests::the_measured_consumer_reading -- --nocapture`.
#[test]
fn the_measured_consumer_reading() {
    use std::collections::BTreeMap;

    use crate::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
    use crate::physical_constraint_grading::EdgeProvenance;
    use crate::rigidity_receiver::{ExactConfiguration, RigidityJacobian, rigidity_reading};

    let Some(request) = std::env::var_os(CONSUMER_ENV) else {
        return;
    };
    let request = request.to_string_lossy().to_string();
    for extent in request
        .split(',')
        .filter_map(|value| value.trim().parse::<usize>().ok())
    {
        assert!(
            extent.is_multiple_of(3),
            "a coordinate extent is three per occurrence"
        );
        let points = extent / 3;
        let started = std::time::Instant::now();
        let places = lattice_places(points);
        let grain = Rat::from_integer(BigInt::from(GRAIN));
        let configuration = ExactConfiguration::declared(
            3,
            places.iter().enumerate().map(|(at, place)| {
                (
                    ConstraintVertexId(at as u64 + 1),
                    place
                        .iter()
                        .map(|axis| Rat::from_integer(BigInt::from(*axis)) / &grain)
                        .collect::<Vec<Rat>>(),
                )
            }),
        )
        .expect("a declared configuration");
        let mut constraints = BTreeMap::new();
        for left in 0..points {
            for right in (left + 1)..points {
                let backbone = right == left + 1;
                if !backbone && separation(&places[left], &places[right]) > APERTURE_SQUARED {
                    continue;
                }
                let (edge, _) = ConstraintEdge::new(
                    ConstraintVertexId(left as u64 + 1),
                    ConstraintVertexId(right as u64 + 1),
                )
                .expect("a declared edge");
                constraints.insert(
                    edge,
                    if backbone {
                        EdgeProvenance::Polygonal
                    } else {
                        EdgeProvenance::AdmittedContact
                    },
                );
            }
        }
        let jacobian = RigidityJacobian::found("lattice", &configuration, &constraints)
            .expect("the consumer's own Jacobian");
        let prepared = started.elapsed();
        eprintln!(
            "[consumer] {extent} coordinates, {} constraints, Jacobian built in {:.3} s",
            jacobian.constraint_count(),
            prepared.as_secs_f64()
        );

        let started = std::time::Instant::now();
        let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
        eprintln!(
            "[consumer] {extent} coordinates: rank {}, dim ker J {}, dim coker J {}, \
             internal motions {}, whole reading {:.3} s",
            reading.rank,
            reading.motion_dimension,
            reading.self_stress_dimension,
            reading.internal_motion_dimension,
            started.elapsed().as_secs_f64()
        );
    }
}
