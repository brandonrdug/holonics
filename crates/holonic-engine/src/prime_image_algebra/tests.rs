//! What the certified reading owes, checked on material that can refuse it.
//!
//! The measurement at the end is a **normal test** gated by an environment variable rather than an
//! `#[ignore]`, so the default `cargo test -p holonic-engine --lib prime_image_algebra::` run stays
//! fast and the measured staircase is taken by the same command with the variable set.

use super::*;
use crate::exact_linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;

/// The environment variable that turns the measurement on, and the coordinate extents it takes.
const MEASURE_ENV: &str = "HOLONICS_PRIME_IMAGE_MEASURE";
/// The same, for the reading taken through the real `rigidity_receiver` consumer.
const CONSUMER_ENV: &str = "HOLONICS_PRIME_IMAGE_CONSUMER";

/// The lattice geometry both the fixture Jacobian and the consumer reading are built from.
const SPACING: i64 = 3_800;
const APERTURE_SQUARED: i64 = 8_000 * 8_000;
const GRAIN: i64 = 1_000;

/// A serpentine lattice path of `points` occurrences with a deterministic sub-lattice jitter.
///
/// Consecutive occurrences are neighbours and the path stays compact, so a point carries on the
/// order of eighteen contacts inside the aperture — the density of a folded chain rather than of a
/// free walk. The jitter is far below the spacing: it makes the placement generic without changing
/// which pairs fall inside the aperture.
pub(super) fn lattice_places(points: usize) -> Vec<[i64; 3]> {
    let side = (1i64..).find(|side| side * side * side >= points as i64).unwrap_or(1);
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

/// **The rank by textbook rational Gauss–Jordan, reached without the public API.**
///
/// [definition] This is the baseline the measurement compares against, and it has to be written
/// out here rather than called through [`ExactRatMatrix::rank`]: above
/// [`crate::exact_linear::DECLARED_PRIME_IMAGE_CROSSOVER`] that entry *is* the certified path, so
/// calling it would have compared the certified reading against itself. The loop below is the one
/// `exact_linear::reduced_row_echelon` runs below the crossover, entry for entry.
pub(super) fn rational_rank(matrix: &ExactRatMatrix) -> usize {
    let rows = matrix.rows();
    let columns = matrix.columns();
    let mut working = matrix.to_rows();
    let mut pivots = 0usize;
    for column in 0..columns {
        if pivots >= rows {
            break;
        }
        let Some(found) = (pivots..rows).find(|row| !working[*row][column].is_zero()) else {
            continue;
        };
        working.swap(found, pivots);
        let divisor = working[pivots][column].clone();
        for entry in &mut working[pivots] {
            *entry /= &divisor;
        }
        let pivot = working[pivots].clone();
        for row in 0..rows {
            if row == pivots || working[row][column].is_zero() {
                continue;
            }
            let factor = working[row][column].clone();
            for (entry, above) in working[row].iter_mut().zip(&pivot) {
                *entry -= &factor * above;
            }
        }
        pivots += 1;
    }
    pivots
}

/// The exact squared separation of two lattice places, in the lattice's own integer units.
pub(super) fn separation(left: &[i64; 3], right: &[i64; 3]) -> i64 {
    (0..3)
        .map(|axis| {
            let difference = left[axis] - right[axis];
            difference * difference
        })
        .sum()
}

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|value| rat(*value, 1)).collect())
            .collect(),
    )
    .expect("a rectangular fixture")
}

// ===============================================================================================
// the presentation and its decoder
// ===============================================================================================

#[test]
fn clearing_denominators_records_a_nonzero_scale_and_the_decoder_returns_the_original_row() {
    let map = ExactRatMatrix::new(vec![
        vec![rat(1, 2), rat(1, 3), rat(0, 1)],
        vec![rat(6, 1), rat(-9, 1), rat(3, 1)],
        vec![rat(0, 1), rat(0, 1), rat(0, 1)],
    ])
    .expect("a rectangular fixture");
    let presentation = IntegralPresentation::of(&map).expect("the presentation clears");

    // `1/2, 1/3, 0` clears to `3, 2, 0` — the common denominator six, with no content to divide out.
    assert_eq!(*presentation.entry(0, 0).expect("entry"), BigInt::from(3));
    assert_eq!(*presentation.entry(0, 1).expect("entry"), BigInt::from(2));
    // `6, -9, 3` has content three, so the scale is `1/3` and the row is primitive.
    assert_eq!(*presentation.entry(1, 0).expect("entry"), BigInt::from(2));
    assert_eq!(*presentation.entry(1, 2).expect("entry"), BigInt::from(1));

    for row in 0..map.rows() {
        assert!(
            !presentation.row_scale(row).expect("scale").is_zero(),
            "a scale is invertible or it is not a scale"
        );
        assert_eq!(
            presentation.decoded_row(row).expect("decoded"),
            map.row(row).expect("row").to_vec(),
            "the decoder returns the original row exactly"
        );
    }
}

#[test]
fn the_scaled_target_is_the_one_the_cleared_map_solves_against() {
    let map = ExactRatMatrix::new(vec![vec![rat(1, 2), rat(1, 4)], vec![rat(1, 3), rat(1, 1)]])
        .expect("a rectangular fixture");
    let presentation = IntegralPresentation::of(&map).expect("the presentation clears");
    let target = vec![rat(1, 1), rat(2, 1)];
    let scaled = presentation.scaled_target(&target).expect("scaled");
    // `B x = diag(s) b` is the same system as `A x = b`, so a solution of one solves the other.
    for row in 0..map.rows() {
        let scale = presentation.row_scale(row).expect("scale");
        assert_eq!(scaled[row], &target[row] * scale);
    }
}

// ===============================================================================================
// the charts
// ===============================================================================================

#[test]
fn the_first_chart_is_the_cards_own_ring_and_a_composite_modulus_is_refused() {
    let device = PrimeChart::device().expect("the device chart is admissible");
    assert_eq!(device.modulus(), mount::ModularWords::DEVICE.modulus());
    assert_eq!(device.modulus(), (1u64 << 61) - 1);

    let charts = descending_charts(4).expect("four charts");
    assert_eq!(charts[0].modulus(), device.modulus());
    for pair in charts.windows(2) {
        assert!(pair[0].modulus() > pair[1].modulus(), "descending, deterministic");
    }

    // `2^61 - 3` is composite; the declaration is decided, never trusted.
    assert!(matches!(
        PrimeChart::declared((1u64 << 61) - 3),
        Err(PrimeImageRefusal::ModulusNotPrime(_))
    ));
    assert!(matches!(
        PrimeChart::declared(7),
        Err(PrimeImageRefusal::ModulusWindow { .. })
    ));
    assert!(matches!(
        PrimeChart::declared(u64::MAX),
        Err(PrimeImageRefusal::ModulusWindow { .. })
    ));
}

#[test]
fn the_charts_arithmetic_is_the_rings_and_inversion_is_exact() {
    let chart = PrimeChart::device().expect("device chart");
    let modulus = chart.modulus();
    for value in [1u64, 2, 3, 1_000_003, modulus - 1] {
        assert_eq!(chart.mul(value, chart.invert(value)), 1 % modulus);
    }
    assert_eq!(chart.sub(3, 5), modulus - 2);
}

// ===============================================================================================
// the lift
// ===============================================================================================

#[test]
fn the_hoisted_lift_agrees_with_the_pair_law_it_specialises() {
    use crate::arithmetic_fiber::{ExactCongruence, chinese_remainder_pair};

    let charts = descending_charts(3).expect("three charts");
    let values: Vec<u64> = vec![17, 0, 4_000_000_001, 999];
    let mut accumulator = CrtAccumulator::new(values.len());
    let mut combined: Option<Vec<ExactCongruence>> = None;

    for chart in &charts {
        let modulus = chart.modulus();
        let image: Vec<u64> = values.iter().map(|value| value % modulus).collect();
        accumulator.absorb(&image, modulus);
        combined = Some(match combined {
            None => image
                .iter()
                .map(|residue| {
                    ExactCongruence::new(BigInt::from(*residue), BigInt::from(modulus))
                        .expect("a congruence")
                })
                .collect(),
            Some(standing) => standing
                .into_iter()
                .zip(&image)
                .map(|(left, residue)| {
                    chinese_remainder_pair(
                        left,
                        ExactCongruence::new(BigInt::from(*residue), BigInt::from(modulus))
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
            accumulator.residues[at], congruence.residue,
            "the hoisted lift is the pair law with the Bezout coefficient taken out of the loop"
        );
        assert_eq!(accumulator.modulus, congruence.modulus);
    }

    // And the lift is faithful: every original value reconstructs once the window admits it.
    let reconstructed = accumulator.reconstruct().expect("the window admits these");
    for (at, value) in values.iter().enumerate() {
        assert_eq!(reconstructed[at], Rat::from_integer(BigInt::from(*value)));
    }
}

#[test]
fn a_rational_entry_reconstructs_and_the_square_root_bound_is_the_one_that_admits_it() {
    assert_eq!(integer_square_root(&BigInt::from(0)), BigInt::zero());
    assert_eq!(integer_square_root(&BigInt::from(99)), BigInt::from(9));
    assert_eq!(integer_square_root(&BigInt::from(100)), BigInt::from(10));
    assert_eq!(
        integer_square_root(&(BigInt::one() << 200)),
        BigInt::one() << 100
    );

    // `-3/7` as a residue in one chart, lifted and recovered.
    let chart = PrimeChart::device().expect("device chart");
    let modulus = chart.modulus();
    let residue = chart.mul(modulus - 3, chart.invert(7));
    let mut accumulator = CrtAccumulator::new(1);
    accumulator.absorb(&[residue], modulus);
    let recovered = accumulator.reconstruct().expect("a reconstruction");
    assert_eq!(recovered[0], rat(-3, 7));
}

// ===============================================================================================
// the certificate
// ===============================================================================================

#[test]
fn a_singular_map_returns_a_certified_rank_and_an_independent_exhibited_kernel() {
    let map = matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]);
    let certificate = certified_kernel(&map).expect("a certified reading");

    assert_eq!(certificate.rank(), 2);
    assert_eq!(certificate.pivot_columns(), &[0, 1]);
    assert_eq!(certificate.free_columns(), &[2]);
    assert_eq!(certificate.kernel().len(), 1);

    // The certificate carries both halves and re-checks against the caller's own matrix.
    certificate.verify(&map).expect("the certificate verifies");

    // `rank >= r` is a nonzero minor in a named chart, on named rows.
    let (modulus, rows, determinant) = certificate.minor();
    assert!(determinant != 0, "a vanishing minor certifies no rank");
    assert_eq!(rows.len(), 2);
    assert!(modulus >= DECLARED_PRIME_FLOOR);

    // `rank <= r` is the exhibited kernel, and it agrees with the rational carrier's own answer.
    assert_eq!(certificate.kernel(), map.kernel_basis().expect("kernel"));
    assert_eq!(certificate.rank(), map.rank().expect("rank"));
}

#[test]
fn the_echelon_form_the_certificate_determines_is_the_carriers_own() {
    for fixture in [
        matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]),
        matrix(&[&[0, 0, 1, 2], &[0, 0, 2, 4], &[3, 0, 0, 1]]),
        matrix(&[&[2, 4], &[1, 2], &[3, 6]]),
        matrix(&[&[1, 0], &[0, 1]]),
        matrix(&[&[0, 0], &[0, 0]]),
    ] {
        let certificate = certified_kernel(&fixture).expect("a certified reading");
        certificate.verify(&fixture).expect("verified");
        let (reduced, pivots, _) = fixture.reduced_row_echelon().expect("the rational reduction");
        assert_eq!(
            certificate.reduced_rows(),
            reduced.to_rows(),
            "the echelon form is determined by the kernel and the pivot set, at no further \
             reconstruction cost"
        );
        assert_eq!(certificate.pivot_columns(), pivots.as_slice());
    }
}

#[test]
fn the_leftmost_greedy_clause_is_what_separates_the_two_bases_of_one_kernel() {
    // `[1 1]` has two normalised bases of one kernel, under two different pivot sets. Only the
    // leftmost-greedy one passes the structural clause, and it is the one the API names.
    let map = matrix(&[&[1, 1]]);
    let certificate = certified_kernel(&map).expect("a certified reading");
    assert_eq!(certificate.pivot_columns(), &[0]);
    assert_eq!(certificate.kernel(), &[vec![rat(-1, 1), rat(1, 1)]]);
    certificate.verify(&map).expect("verified");

    // The other basis is a basis of the same kernel and is normalised on its own free coordinate,
    // yet it names pivot `{1}`, and the clause refuses it.
    let presentation = IntegralPresentation::of(&map).expect("presentation");
    let mut spent = 0u64;
    let refusal = verify_kernel(
        &presentation,
        1,
        &[1],
        &[0],
        &[vec![rat(1, 1), rat(-1, 1)]],
        &mut spent,
    )
    .expect_err("the leftmost clause refuses the right-handed pivot set");
    assert!(matches!(
        refusal,
        PrimeImageRefusal::PivotProfileNotLeftmost { free: 0, pivot: 1 }
    ));
}

#[test]
fn a_zero_or_duplicated_kernel_vector_certifies_nothing_and_is_refused() {
    let map = matrix(&[&[1, 1, 1], &[0, 0, 0]]);
    let presentation = IntegralPresentation::of(&map).expect("presentation");
    let mut spent = 0u64;

    // Two copies of one genuine kernel vector: both satisfy `A N = 0`, and the normalisation
    // clause is exactly what refuses them.
    let duplicated = vec![
        vec![rat(-1, 1), rat(1, 1), rat(0, 1)],
        vec![rat(-1, 1), rat(1, 1), rat(0, 1)],
    ];
    assert!(matches!(
        verify_kernel(&presentation, 1, &[0], &[1, 2], &duplicated, &mut spent),
        Err(PrimeImageRefusal::KernelNormalisation { .. })
    ));

    // A zero vector likewise.
    let zeroed = vec![
        vec![rat(-1, 1), rat(1, 1), rat(0, 1)],
        vec![rat(0, 1), rat(0, 1), rat(0, 1)],
    ];
    assert!(matches!(
        verify_kernel(&presentation, 1, &[0], &[1, 2], &zeroed, &mut spent),
        Err(PrimeImageRefusal::KernelNormalisation { .. })
    ));

    // And a vector that is normalised but not in the kernel is caught by the exact residual.
    let wrong = vec![
        vec![rat(-2, 1), rat(1, 1), rat(0, 1)],
        vec![rat(-1, 1), rat(0, 1), rat(1, 1)],
    ];
    assert!(matches!(
        verify_kernel(&presentation, 1, &[0], &[1, 2], &wrong, &mut spent),
        Err(PrimeImageRefusal::KernelResidualNonzero { vector: 0, row: 0 })
    ));
}

#[test]
fn a_vanishing_minor_is_refused_rather_than_read_as_a_rank() {
    let map = matrix(&[&[1, 2], &[2, 4]]);
    let presentation = IntegralPresentation::of(&map).expect("presentation");
    let chart = PrimeChart::device().expect("device chart");
    let mut spent = 0u64;
    // Rows `{0, 1}` against columns `{0, 1}` is a singular 2x2 minor: it certifies no rank 2.
    assert!(matches!(
        verify_minor(&presentation, &chart, &[0, 1], &[0, 1], &mut spent),
        Err(PrimeImageRefusal::MinorVanishes { rank: 2, .. })
    ));
    // The map's honest rank is one, and that minor does not vanish.
    verify_minor(&presentation, &chart, &[0], &[0], &mut spent).expect("a 1x1 minor");
}

#[test]
fn a_certificate_does_not_transfer_to_another_matrix() {
    let map = matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]);
    let certificate = certified_kernel(&map).expect("a certified reading");
    let other = matrix(&[&[1, 2, 3], &[2, 4, 7], &[1, 1, 1]]);
    assert!(
        certificate.verify(&other).is_err(),
        "a remount re-validates; a certificate is not a token"
    );
    let wider = matrix(&[&[1, 2, 3, 4], &[2, 4, 6, 8], &[1, 1, 1, 1]]);
    assert!(matches!(
        certificate.verify(&wider),
        Err(PrimeImageRefusal::ShapeDisagrees { .. })
    ));
}

#[test]
fn a_map_with_a_bad_chart_still_returns_and_names_the_chart_it_refused() {
    // `det [[1, 1], [1, 1 + p]] = p`, so the map has rank two over Q and rank one in the device's
    // own chart: a genuinely bad prime, not one the content division would have removed — both
    // rows are primitive. The reading returns anyway, and the refusal is retained, not dropped.
    let modulus = mount::ModularWords::DEVICE.modulus();
    let map = ExactRatMatrix::new(vec![
        vec![rat(1, 1), rat(1, 1)],
        vec![
            rat(1, 1),
            Rat::from_integer(BigInt::from(modulus) + BigInt::one()),
        ],
    ])
    .expect("a rectangular fixture");
    let certificate = certified_kernel(&map).expect("a certified reading");
    certificate.verify(&map).expect("verified");
    assert_eq!(certificate.rank(), 2);
    assert!(
        certificate
            .refused_moduli()
            .iter()
            .any(|(refused, reason)| *refused == modulus
                && matches!(reason, BadChart::RankBelowMaximum { .. })),
        "the bad chart is named: {:?}",
        certificate.refused_moduli()
    );
}

#[test]
fn a_rational_map_with_real_denominators_reconstructs_exactly() {
    let map = ExactRatMatrix::new(vec![
        vec![rat(1, 3), rat(2, 5), rat(7, 11)],
        vec![rat(-4, 9), rat(1, 2), rat(0, 1)],
    ])
    .expect("a rectangular fixture");
    let certificate = certified_kernel(&map).expect("a certified reading");
    certificate.verify(&map).expect("verified");
    assert_eq!(certificate.rank(), 2);
    assert_eq!(certificate.kernel(), map.kernel_basis().expect("kernel"));
}

// ===============================================================================================
// the fibre
// ===============================================================================================

#[test]
fn a_consistent_system_returns_the_fibre_and_an_inconsistent_one_returns_the_rank_increase() {
    let map = matrix(&[&[1, 1, 0], &[0, 1, 1]]);
    let target = vec![rat(2, 1), rat(3, 1)];
    let (fibre, certificate) = certified_fibre(&map, &target).expect("a certified fibre");
    let (particular, kernel) = fibre.expect("this system is consistent");
    assert_eq!(map.apply(&particular).expect("applied"), target);
    assert_eq!(kernel, map.kernel_basis().expect("kernel"));
    certificate
        .verify(
            &ExactRatMatrix::shaped(2, 4, {
                let mut rows = map.to_rows();
                for (row, value) in rows.iter_mut().zip(&target) {
                    row.push(value.clone());
                }
                rows
            })
            .expect("augmented"),
        )
        .expect("the augmented certificate verifies");
    assert_eq!(
        Some((particular, kernel)),
        map.preimage_fibre(&target).expect("the carrier's own fibre")
    );

    // A target outside the image: the augmented column becomes a pivot, so the rank rises by one.
    let narrow = matrix(&[&[1, 0], &[0, 1], &[1, 1]]);
    let outside = vec![rat(1, 1), rat(1, 1), rat(3, 1)];
    let (fibre, certificate) = certified_fibre(&narrow, &outside).expect("a certified fibre");
    assert!(fibre.is_none());
    assert_eq!(certificate.rank(), 3);
    assert_eq!(certificate.pivot_columns(), &[0, 1, 2]);
    assert_eq!(
        narrow.rank().expect("rank"),
        2,
        "the unaugmented rank is one lower, which is the incompatibility"
    );
    assert!(narrow.preimage_fibre(&outside).expect("carrier").is_none());
}

// ===============================================================================================
// placement, cost and account
// ===============================================================================================

#[test]
fn the_placement_is_declared_to_the_cover_and_the_device_arm_is_reported_absent() {
    let map = matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]);
    let certificate =
        certified_kernel_over(&map, &crate::hardware_cover::HardwareCover::cpu_only())
            .expect("a certified reading");
    let placement = certificate.placement();
    assert!(!placement.device_carried, "no image is on the card today");
    assert_eq!(placement.sections.len(), 1);
    assert_eq!(placement.sections[0].0, "cpu");
    assert!(placement.mode.contains("prime_image_algebra::certified_kernel"));
    assert!(placement.mode.contains("exact-integer"));

    // The serial span of one image is its pivot count, whatever the placement.
    assert_eq!(certificate.cost().dependency_span, certificate.rank() as u64);

    let account = account(&certificate);
    for coordinate in [
        "prepared-entries",
        "charts-decided",
        "image-multiplications",
        "lifted-entries",
        "reconstruction-attempts",
        "reconstructed-entries",
        "verification-multiplications",
        "readout-entries",
        "dependency-span",
    ] {
        assert!(account.contains_key(coordinate), "{coordinate} is accounted");
    }
    assert_eq!(account.get("device-carried").map(String::as_str), Some("false"));
}

#[test]
fn a_declared_extent_past_the_ceiling_is_refused_before_any_allocation() {
    let refusal = bounded_words("a certified reading", usize::MAX, 2)
        .expect_err("an overflowing extent is refused");
    assert!(matches!(refusal, PrimeImageRefusal::ImageExtent { .. }));
    let refusal = bounded_words("a certified reading", DECLARED_IMAGE_EXTENT_CEILING, 2)
        .expect_err("a product past the ceiling is refused");
    assert!(matches!(refusal, PrimeImageRefusal::ImageExtent { .. }));
    bounded_words("a certified reading", 1024, 1024).expect("a lawful extent");
}

// ===============================================================================================
// the measured staircase
// ===============================================================================================

/// A bar-and-joint rigidity Jacobian of the species the M5 consumers read.
///
/// `holonic_chain::tests::measured_jacobian` builds its rows from alpha-carbon places at a derived
/// decimal grain, joining the backbone and **every pair inside a contact aperture**. This fixture
/// reproduces that species without the authenticated release: occurrences sit on a serpentine
/// lattice path at a 3.8-unit spacing with a deterministic sub-lattice jitter that keeps the frame
/// generic, coordinates carry the denominator `1000` the decimal grain produces, and a constraint
/// is declared for the backbone and for every pair inside an 8.0-unit aperture — so a point
/// carries on the order of eighteen contacts and the Jacobian is as dense and as coefficient-heavy
/// as the measured one, rather than banded.
pub(super) fn rigidity_jacobian(points: usize) -> ExactRatMatrix {
    let places = lattice_places(points);
    let columns = 3 * points;
    let grain = Rat::from_integer(BigInt::from(GRAIN));
    let mut rows: Vec<Vec<Rat>> = Vec::new();
    for left in 0..points {
        for right in (left + 1)..points {
            let backbone = right == left + 1;
            if !backbone && separation(&places[left], &places[right]) > APERTURE_SQUARED {
                continue;
            }
            let mut row = vec![Rat::zero(); columns];
            for axis in 0..3 {
                let difference =
                    Rat::from_integer(BigInt::from(places[left][axis] - places[right][axis]))
                        / &grain;
                row[3 * left + axis] = difference.clone();
                row[3 * right + axis] = -difference;
            }
            rows.push(row);
        }
    }
    ExactRatMatrix::shaped(rows.len(), columns, rows).expect("a rectangular Jacobian")
}

#[test]
fn the_certified_reading_agrees_with_the_rational_carrier_on_a_rigidity_jacobian() {
    // Small enough that the rational carrier still returns, which is the only scope in which the
    // two can be held against each other at all.
    let jacobian = rigidity_jacobian(12);
    let certificate = certified_kernel(&jacobian).expect("a certified reading");
    certificate.verify(&jacobian).expect("verified");
    assert_eq!(certificate.rank(), jacobian.rank().expect("rational rank"));
    assert_eq!(
        certificate.kernel(),
        jacobian.kernel_basis().expect("rational kernel")
    );
    let (reduced, pivots, _) = jacobian.reduced_row_echelon().expect("rational reduction");
    assert_eq!(certificate.reduced_rows(), reduced.to_rows());
    assert_eq!(certificate.pivot_columns(), pivots.as_slice());
}

/// **The measured staircase.** Off by default; taken with
/// `HOLONICS_PRIME_IMAGE_MEASURE=72,120,180,324,612 cargo test --release -p holonic-engine --lib
/// prime_image_algebra::tests::the_measured_staircase -- --nocapture`.
///
/// Every stage is clocked separately, and the clock only reports: the returned certificate's own
/// cost coordinates are the work, and they decide nothing here.
///
/// **The four `as_secs_f64` calls below are the only floating values anywhere in this owner**, and
/// they are accounted here rather than found later: each one formats one elapsed duration onto
/// stderr inside `#[cfg(test)]`. Nothing reads them, no branch depends on them, and no value
/// returned by this module carries one — the standing invariant is about a carrying or deciding
/// path, and a printed clock is neither.
#[test]
fn the_measured_staircase() {
    let Some(request) = std::env::var_os(MEASURE_ENV) else {
        // Not a silent pass: the law under test is checked without the measurement by every test
        // above, and the measurement is a receipt, not a property.
        return;
    };
    let request = request.to_string_lossy().to_string();
    let rational = std::env::var_os("HOLONICS_PRIME_IMAGE_RATIONAL").is_some();
    for extent in request.split(',').filter_map(|value| value.trim().parse::<usize>().ok()) {
        assert!(extent.is_multiple_of(3), "a coordinate extent is three per occurrence");
        let points = extent / 3;
        let started = std::time::Instant::now();
        let jacobian = rigidity_jacobian(points);
        let built = started.elapsed();
        eprintln!(
            "[measured] {extent} coordinates, {} constraints, built in {:.3} s",
            jacobian.rows(),
            built.as_secs_f64()
        );

        let started = std::time::Instant::now();
        let certificate = match certified_kernel(&jacobian) {
            Ok(certificate) => certificate,
            Err(refusal) => {
                eprintln!("[measured] {extent} coordinates: certified reading refused: {refusal}");
                continue;
            }
        };
        let certified = started.elapsed();
        let started = std::time::Instant::now();
        certificate.verify(&jacobian).expect("the certificate verifies");
        let reverified = started.elapsed();
        eprintln!(
            "[measured] {extent} coordinates: certified rank {} nullity {} in {:.3} s, \
             independent re-verification {:.3} s, charts lifted {} refused {}",
            certificate.rank(),
            certificate.kernel().len(),
            certified.as_secs_f64(),
            reverified.as_secs_f64(),
            certificate.image_moduli().len(),
            certificate.refused_moduli().len(),
        );
        for (name, value) in account(&certificate) {
            eprintln!("[measured]   {name} = {value}");
        }

        if rational {
            let started = std::time::Instant::now();
            let rank = rational_rank(&jacobian);
            eprintln!(
                "[measured] {extent} coordinates: rational Gauss-Jordan rank {rank} in {:.3} s",
                started.elapsed().as_secs_f64()
            );
        }
    }
}

/// **The same target read through the real consumer.**
///
/// `rigidity_receiver::rigidity_reading` is one of the two consumers Issue #50 measures, and this
/// owner edits nothing in it: the Jacobian below is built through that module's own
/// `ExactConfiguration` and `ConstraintEdge` constructors, from the same lattice places
/// [`rigidity_jacobian`] uses, and the reading is taken by the public function unchanged.
///
/// The consumer performs **three** separate reductions — `rank`, `kernel_basis` and
/// `cokernel_annihilator` — and then checks rank–nullity, the cokernel count and Maxwell's
/// identity against each other. Those three checks are an independent cross-examination of the
/// certified path: a wrong rank or a short kernel fails them.
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

/// **The certified path reaches the stiffness species, not only the Jacobian species.**
///
/// [measured] The Wave 10 reviewer asked whether `conditioned_static_response`'s ~1 s solves meant
/// the certified reading was refusing `K = J* W J` and silently falling back. It is not: the
/// primary measured the real M5 arm stiffness at **122-bit** widest coefficient against the
/// Jacobian's **13**, and a certified rank of it at **5 ms**. The elimination is 0.7 % of that
/// consumer's cost; the wide-rational arithmetic downstream of it is the rest. This holds the part
/// of that finding which belongs in the suite: the two species both reach the certified path, and
/// a regression that made the stiffness species fall back would be caught here rather than in a
/// wall-clock somebody has to notice.
#[test]
fn the_certified_path_reaches_the_stiffness_species() {
    let jacobian = rigidity_jacobian(20);
    let extent = jacobian.columns();
    assert!(extent >= crate::exact_linear::DECLARED_PRIME_IMAGE_CROSSOVER);

    // K = J* W J with the weight species the elastic declaration uses: gamma / (4 * squared
    // length), which is what puts a squared length into every entry's denominator.
    let transpose = jacobian.transpose().expect("a transpose");
    let mut weighted = jacobian.to_rows();
    for (row, entries) in weighted.iter_mut().enumerate() {
        let weight = Rat::new(
            BigInt::from((row as i64 % 7) + 3),
            BigInt::from(4 * ((row as i64 % 5) + 2)),
        );
        for entry in entries.iter_mut() {
            *entry *= &weight;
        }
    }
    let weighted = ExactRatMatrix::shaped(jacobian.rows(), jacobian.columns(), weighted)
        .expect("a weighted jacobian");
    let stiffness = transpose.multiply(&weighted).expect("K = J* W J");
    assert_eq!(stiffness.rows(), extent);

    let widest = |matrix: &ExactRatMatrix| {
        matrix
            .entries()
            .iter()
            .map(|entry| entry.numer().bits().max(entry.denom().bits()))
            .max()
            .unwrap_or(0)
    };
    assert!(
        widest(&stiffness) > widest(&jacobian),
        "the weighting is what widens the coefficients, and that is the species under test"
    );

    let certified = certified_kernel(&stiffness);
    assert!(
        certified.is_ok(),
        "the certified path refused the stiffness species: {:?}",
        certified.err()
    );
    let certificate = certified.expect("certified");
    certificate
        .verify(&stiffness)
        .expect("and it verifies against that very matrix");
    assert_eq!(
        certificate.rank(),
        stiffness.rank().expect("the public reading agrees"),
    );
}
