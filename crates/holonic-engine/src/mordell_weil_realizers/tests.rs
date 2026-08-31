//! Controls for the realizer family, graded against published record curves.
//!
//! Every figure asserted here was read from the ICARM elliptic-curve rank leaderboard's published
//! database on 2026-08-26. They are exterior testimony and that is exactly what makes them a
//! control: the family is rebuilt here from its six published values and its specialization, and
//! the minimal model that comes out must equal the one the leaderboard verified independently.

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use std::str::FromStr;

fn rational(values: [i64; 6]) -> [BigRational; 6] {
    values.map(|v| BigRational::from_integer(BigInt::from(v)))
}

fn big(text: &str) -> BigInt {
    BigInt::from_str(text).expect("literal")
}

#[test]
fn the_published_record_sextuples_lie_on_the_variety() {
    // #159 (rank 17), #161 (rank 18), #280 (rank 19). Published as-is except #280, which the
    // leaderboard reports in its translated "canonical primitive" form.
    assert!(RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830])).is_ok());
    assert!(RealizerSextuple::found(rational([348, -600, -216, 492, 876, -900])).is_ok());
    assert!(
        RealizerSextuple::found_after_centring(rational([0, 1075, 1394, 2291, 4186, 4824])).is_ok()
    );
}

#[test]
fn a_trace_zero_sextuple_off_the_variety_is_refused_by_the_second_identity() {
    // Trace zero alone is not the condition: this one clears `e_1 = 0` and fails `2e_5 = e_2 e_3`.
    let refusal = RealizerSextuple::found(rational([1, 2, 3, -4, -5, 3])).unwrap_err();
    assert!(matches!(
        refusal,
        SextupleRefusal::RepeatedValue { .. } | SextupleRefusal::RemainderObstruction { .. }
    ));
    let refusal = RealizerSextuple::found(rational([1, 2, 5, -3, -4, -1])).unwrap_err();
    match refusal {
        SextupleRefusal::RemainderObstruction { residual } => assert!(!residual.is_zero()),
        other => panic!("expected the degree-five obstruction, got {other:?}"),
    }
}

#[test]
fn a_sextuple_of_nonzero_trace_is_refused_by_the_first_identity() {
    let refusal = RealizerSextuple::found(rational([1, 2, 3, 4, 5, 6])).unwrap_err();
    assert!(matches!(refusal, SextupleRefusal::TraceNotZero { .. }));
}

#[test]
fn the_remainder_is_a_quartic_and_every_forced_realizer_lands_on_it() {
    let family = RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830]))
        .expect("on the variety");
    let quartic = family.remainder_at(&BigRational::from_integer(BigInt::from(2454)));
    assert_eq!(quartic.forced_realizers.len(), 12);
    assert!(!quartic.coefficient[4].is_zero(), "degree is exactly four");
    for (x, y) in quartic.forced_realizers.iter() {
        let mut value = BigRational::zero();
        for c in quartic.coefficient.iter().rev() {
            value = value * x + c;
        }
        assert_eq!(value, y * y, "forced realizer off the quartic at x = {x}");
    }
}

/// The control that grades the whole chain: rebuild the family the leaderboard published for
/// curve #159, and the minimal model must be the one it verified.
#[test]
fn rebuilding_curve_159_reproduces_its_published_minimal_model() {
    let primes = primes_upto(100_000);
    let family = RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830]))
        .expect("on the variety");
    let quartic = family
        .remainder_at(&BigRational::from_integer(BigInt::from(2454)))
        .integral(&primes);
    let (c4, c6) = quartic.invariants();
    let minimal = minimalise(&c4, &c6, &primes);
    assert_eq!(minimal.c4, big("63443960979800259369"));
    assert_eq!(minimal.c6, big("-213981041085997763351391274197"));
    // and the published a-invariants [1, -1, 0, a4, a6]
    assert_eq!(minimal.a_invariants[0], BigInt::from(1));
    assert_eq!(minimal.a_invariants[3], big("-1321749187079172070"));
    assert_eq!(minimal.a_invariants[4], big("247663242328119893241310696"));
}

#[test]
fn the_height_key_orders_the_published_records_the_way_their_logarithms_do() {
    let primes = primes_upto(100_000);
    let build = |values: [i64; 6], num: i64, den: i64| {
        let family = RealizerSextuple::found_after_centring(rational(values)).expect("variety");
        let t = BigRational::new(BigInt::from(num), BigInt::from(den));
        let quartic = family.remainder_at(&t).integral(&primes);
        let (c4, c6) = quartic.invariants();
        minimalise(&c4, &c6, &primes).naive_height_key()
    };
    // #159 log h = 136.7901, #161 log h = 193.0789, #280 log h = 199.2905
    let a = build([-1146, -2304, -654, 3054, 2880, -1830], 2454, 1);
    let b = build([348, -600, -216, 492, 876, -900], 17142, 23);
    let c = build([0, 1075, 1394, 2291, 4186, 4824], 2697, 2);
    assert!(a < b, "#159 must be lighter than #161");
    assert!(b < c, "#161 must be lighter than #280");
}

/// The float-free rank certificate, graded on the one population whose answer is a theorem:
/// Mestre's twelve forced realizers satisfy exactly one relation, so they span rank eleven.
#[test]
fn the_forced_realizers_certify_rank_eleven_without_a_height_pairing() {
    let family = RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830]))
        .expect("on the variety");
    let remainder = family.remainder_at(&BigRational::from_integer(BigInt::from(2454)));
    let base = remainder.forced_realizers[0].clone();
    let chart = QuarticChart::through(&remainder.coefficient, &base).expect("a chart exists");
    let mut carried = Vec::new();
    for (x, y) in remainder.forced_realizers.iter() {
        if let Some(point) = chart.carry(x, y) {
            assert!(
                chart.curve.contains(&point.0, &point.1),
                "carried realizer left the curve"
            );
            carried.push(point);
        }
    }
    assert_eq!(
        carried.len(),
        11,
        "one forced realizer is the point at infinity"
    );
    let receivers = primes_upto(4000);
    let certificate = independence_certificate(&chart.curve, &carried, 5, &receivers);
    assert_eq!(certificate.rank_lower_bound, 11);
    assert!(
        certificate.torsion_free,
        "coprime orders witness trivial torsion"
    );
    assert!(!certificate.receivers.is_empty());
}

/// The exact wheel: cells are integer divisions of the crossing ratio, and rolling composes
/// receiver partitions by CRT. Graded on the published rank-17 family, whose specialization the
/// leaderboard names.
#[test]
fn the_rolled_wheel_places_the_published_specialization_in_its_own_top_class_band() {
    let family = RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830]))
        .expect("on the variety");
    let partitions = family.receiver_partitions(&primes_upto(60));
    assert!(partitions.iter().all(|p| p.cell.len() == p.prime as usize));
    let (rolled, deferred) = RolledWheel::roll(&partitions, 200_000);
    assert!(
        rolled.modulus > 1,
        "the wheel must absorb at least one receiver"
    );
    assert_eq!(
        rolled.receivers.len() + deferred.len(),
        partitions.len(),
        "every receiver is either rolled in or reported as deferred"
    );
    // the composite score is exactly the sum of its receivers' cells
    let probe = 2454i64;
    let expected: i64 = partitions
        .iter()
        .filter(|p| rolled.receivers.contains(&p.prime))
        .map(|p| p.cell[probe.rem_euclid(p.prime as i64) as usize])
        .sum();
    assert_eq!(
        rolled.score[(probe as u64 % rolled.modulus) as usize],
        expected
    );
    let admitted = rolled.admitted_classes(8);
    assert_eq!(admitted.len(), 8);
    let best = rolled.score[admitted[0] as usize];
    assert!(
        rolled.score.iter().all(|v| *v <= best),
        "admitted classes lead the exact order"
    );
}

#[test]
fn the_published_height_column_becomes_a_conservative_integer_ceiling() {
    let primes = primes_upto(20_000);
    let family = RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830]))
        .expect("on the variety");
    let quartic = family
        .remainder_at(&BigRational::from_integer(BigInt::from(2454)))
        .integral(&primes);
    let (c4, c6) = quartic.invariants();
    let key = minimalise(&c4, &c6, &primes).naive_height_key();
    // the leaderboard publishes #159 at log h = 136.7901
    let at_its_own_line = height_ceiling_from_published_log(136.7901);
    let above = height_ceiling_from_published_log(136.7902);
    let below = height_ceiling_from_published_log(136.7);
    assert!(
        key <= at_its_own_line,
        "rounding up must never reject the curve at its own line"
    );
    assert!(key < above);
    assert!(key > below);
}

/// The section solver, graded against a published family whose extra sections were first found by
/// fitting and are now *solved*. The six of curve #159 carry denominator 53.
#[test]
fn the_linear_sections_of_the_published_family_are_solved_not_searched() {
    let family = RealizerSextuple::found(rational([-1146, -2304, -654, 3054, 2880, -1830]))
        .expect("on the variety");
    let sections = family.linear_sections();
    let slopes: std::collections::BTreeSet<String> =
        sections.iter().map(|s| s.slope.to_string()).collect();
    assert!(
        slopes.contains("79/53") && slopes.contains("35/53") && slopes.contains("31/53"),
        "the solver must return the three positive slopes, got {slopes:?}"
    );
    for section in sections.iter() {
        let remainder = family.remainder_polynomials();
        let composed = family.remainder_along(&remainder, &section.slope, &section.intercept);
        let mut squared = vec![BigRational::zero(); composed.len()];
        // every returned section must actually be one: r along it is a square
        assert!(
            super::is_perfect_square_for_test(&composed),
            "returned a slope/intercept whose remainder is not a square"
        );
        let _ = &mut squared;
    }
}

/// A sextuple can satisfy every coefficient identity while its quartic has identically vanishing
/// discriminant. Then `r` is a square along *every* line and the "sections" are an artefact of a
/// surface that is not elliptic. The solver must refuse it rather than report hundreds.
#[test]
fn a_degenerate_sextuple_returns_no_sections() {
    // solved from the design elimination: on the variety, trace zero, six distinct values, and
    // discriminant identically zero
    let degenerate =
        RealizerSextuple::found(rational([-65, 13, 52, 67, -20, -47])).expect("on the variety");
    assert!(
        degenerate.linear_sections().is_empty(),
        "a surface with vanishing discriminant must return no sections"
    );
}
