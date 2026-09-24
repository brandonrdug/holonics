//! What the certified reading owes, checked on material that can refuse it.

use super::*;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Zero};

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
fn the_first_chart_is_the_mersenne61_ring_and_a_composite_modulus_is_refused() {
    let mersenne = PrimeChart::mersenne61().expect("the Mersenne chart is admissible");
    assert_eq!(
        mersenne.modulus(),
        crate::ratio::ring::ModularWords::MERSENNE61.modulus()
    );
    assert_eq!(mersenne.modulus(), (1u64 << 61) - 1);

    let charts = descending_charts(4).expect("four charts");
    assert_eq!(charts[0].modulus(), mersenne.modulus());
    for pair in charts.windows(2) {
        assert!(
            pair[0].modulus() > pair[1].modulus(),
            "descending, deterministic"
        );
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
    let chart = PrimeChart::mersenne61().expect("Mersenne chart");
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
fn a_rational_entry_reconstructs_and_the_square_root_bound_is_the_one_that_admits_it() {
    assert_eq!(integer_square_root(&BigInt::from(0)), BigInt::zero());
    assert_eq!(integer_square_root(&BigInt::from(99)), BigInt::from(9));
    assert_eq!(integer_square_root(&BigInt::from(100)), BigInt::from(10));
    assert_eq!(
        integer_square_root(&(BigInt::one() << 200)),
        BigInt::one() << 100
    );

    // `-3/7` as a residue in one chart, lifted and recovered.
    let chart = PrimeChart::mersenne61().expect("Mersenne chart");
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
        let (reduced, pivots, _) = fixture
            .reduced_row_echelon()
            .expect("the rational reduction");
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
    let chart = PrimeChart::mersenne61().expect("Mersenne chart");
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
        "a reuse re-validates; a certificate is not a token"
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
    let modulus = crate::ratio::ring::ModularWords::MERSENNE61.modulus();
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
        map.preimage_fibre(&target)
            .expect("the carrier's own fibre")
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
// declared extents
// ===============================================================================================
