//! The falsifiers of the identity atlas.
//!
//! Every test here is about a statement that could be false. The two that carry the audit's
//! corrections are `a_single_chart_wrongly_certifies_the_galilean_collapse` — a chart family that
//! misses a component certifies a non-identity, and the half-turn winding refuses it with an exact
//! counterexample point — and `the_sampled_rank_is_only_a_lower_bound_before_certification`, which
//! reproduces the contract's own `{1, x, x²}` example at one sample.

use super::*;

fn named(names: &[&str]) -> Vec<String> {
    names.iter().map(|name| (*name).to_owned()).collect()
}

#[test]
fn the_sampled_rank_is_only_a_lower_bound_before_certification() {
    // {1, x, x²} on the affine line, sampled once at x = 0: rank 1, true filtered dimension 3.
    let family = ReceiverFamily::total_degree(&["x"], 2).expect("a one-receiver family");
    assert_eq!(family.monomials().len(), 3);
    let chart = RationalChart::polynomial(
        "the affine line",
        &["x"],
        vec![ExactMultivariate::variable(1, 0).expect("the coordinate")],
    )
    .expect("a polynomial chart");
    let configuration = Configuration::new(
        "the contract's own counterexample",
        family,
        vec![chart],
        "one chart, the whole line",
        3,
        1,
    )
    .expect("a configuration");

    let one_point = vec![(0usize, vec![Rat::zero()])];
    let thin = sample_kernel(&configuration, &one_point).expect("one sample reads");
    assert_eq!(thin.sampled_rank, 1, "one sample sees rank one");
    assert_eq!(thin.kernel.len(), 2, "and two candidate kernel directions");

    let many: Vec<(usize, Vec<Rat>)> = (0..4)
        .map(|value| (0usize, vec![rational(value)]))
        .collect();
    let full = sample_kernel(&configuration, &many).expect("four samples read");
    assert_eq!(full.sampled_rank, 3, "the true filtered dimension is three");
    assert!(
        full.kernel.is_empty(),
        "and the line has no identity at degree two"
    );

    // The thin reading's candidates are refused by exact substitution, which is the whole point.
    let candidates = configuration.candidate_points(32);
    let refusals = thin
        .kernel
        .iter()
        .filter(|vector| {
            certify(&configuration, vector, &candidates)
                .expect("certification runs")
                .is_err()
        })
        .count();
    assert_eq!(
        refusals, 2,
        "every spurious direction is refused, not returned"
    );
}

#[test]
fn the_two_sided_pythagorean_relation_is_the_only_generator_at_its_degree() {
    let configuration = two_sided_angle(2, 1).expect("T0 declares");
    let returned = walk(&configuration).expect("T0 walks");
    assert!(returned.refusals.is_empty(), "no candidate stays refused");
    assert_eq!(
        returned.identities.len(),
        1,
        "exactly one identity at degree (2, 1): {:?}",
        returned
            .identities
            .iter()
            .map(|identity| identity.polynomial.written(&named(&ONE_ANGLE_RECEIVERS)))
            .collect::<Vec<_>>()
    );
    let written = returned.identities[0]
        .polynomial
        .written(&named(&ONE_ANGLE_RECEIVERS));
    // Up to an overall rational scale the generator is C² + k S² − 1: three terms, one of them
    // the constant, one the pure C-square and one the curvature-weighted S-square.
    assert!(
        written.contains("C^2") && written.contains("S^2*Curv"),
        "the generator is C^2 + k S^2 - 1: {written}"
    );
    assert_eq!(
        returned.identities[0].polynomial.term_count(),
        3,
        "three terms and no more: {written}"
    );
    assert_eq!(
        returned.filtered_dimension + returned.redundancy,
        returned.monomials,
        "the cumulative Hilbert dimension and the redundancy partition the declared family"
    );

    // The sampled rank is read by rank-nullity from the kernel's own reduction. `exact_linear`'s
    // own `rank` is taken here independently and must agree; a disagreement would mean the
    // reported filtered dimension is not the one the operator has.
    let points: Vec<(usize, Vec<Rat>)> = configuration
        .candidate_points(64)
        .into_iter()
        .enumerate()
        .filter_map(|(index, point)| {
            let chart = index % configuration.charts().len();
            configuration.charts()[chart]
                .denominator()
                .evaluate(&point)
                .ok()
                .filter(|value| !value.is_zero())
                .map(|_| (chart, point))
        })
        .take(40)
        .collect();
    let matrix = evaluation_matrix(&configuration, &points).expect("the face map evaluates");
    let reading = sample_kernel(&configuration, &points).expect("the kernel reads");
    assert_eq!(
        matrix.rank().expect("exact_linear reads its own rank"),
        reading.sampled_rank,
        "exact_linear::rank and rank-nullity must be the same number"
    );
}

#[test]
fn the_bounded_degree_consequences_are_the_monomial_multiples_of_the_generator() {
    let generator_only = two_sided_angle(2, 1).expect("T0 declares");
    let generator = walk(&generator_only).expect("T0 walks");
    let wider = two_sided_angle(4, 2).expect("the wider T0 declares");
    let consequences = walk(&wider).expect("the wider T0 walks");
    assert!(consequences.refusals.is_empty());
    assert_eq!(
        generator.identities.len(),
        1,
        "one generator at the smaller degree"
    );
    assert_eq!(
        consequences.identities.len(),
        12,
        "and twelve bounded-degree consequences: the monomial multiples m·g with deg(m) <= (2, 1)"
    );
    // Every one of them reduces to zero modulo the single generator, which is what makes them
    // consequences rather than new generators.
    let closure = buchberger(&[generator.identities[0].polynomial.clone()]).expect("closure");
    let completeness =
        bounded_degree_completeness(&consequences.identities, &closure).expect("reduction runs");
    assert!(
        completeness.every_certified_vector_reduces_to_zero,
        "unreduced: {:?}",
        completeness.unreduced
    );
    assert!(
        completeness.remaining_obligation.contains("all degrees"),
        "the all-degree obligation is named, not discharged"
    );
}

#[test]
fn the_addition_laws_are_recovered_uniformly_in_the_curvature() {
    let configuration = two_sided_addition(2, 1).expect("T1 declares");
    let returned = walk(&configuration).expect("T1 walks");
    assert!(returned.refusals.is_empty(), "no candidate stays refused");
    let names = named(&ADDITION_RECEIVERS);
    let written: Vec<String> = returned
        .identities
        .iter()
        .map(|identity| identity.polynomial.written(&names))
        .collect();
    assert!(
        returned.identities.len() >= 4,
        "at least the two Pythagorean relations and the two addition laws: {written:?}"
    );
    // The sine addition law S3 − S1 C2 − C1 S2 is degree (2, 0) and must be in the certified span.
    let family = configuration.family();
    let mut sine_law = ExactMultivariate::zero(family.width());
    let index = |name: &str| {
        names
            .iter()
            .position(|slot| slot == name)
            .expect("a receiver")
    };
    let mut exponents = vec![0u32; family.width()];
    exponents[index("S3")] = 1;
    sine_law = sine_law
        .plus(&ExactMultivariate::term(family.width(), exponents, Rat::one()).expect("a term"))
        .expect("matching shapes");
    let mut first = vec![0u32; family.width()];
    first[index("S1")] = 1;
    first[index("C2")] = 1;
    sine_law = sine_law
        .minus(&ExactMultivariate::term(family.width(), first, Rat::one()).expect("a term"))
        .expect("matching shapes");
    let mut second = vec![0u32; family.width()];
    second[index("C1")] = 1;
    second[index("S2")] = 1;
    sine_law = sine_law
        .minus(&ExactMultivariate::term(family.width(), second, Rat::one()).expect("a term"))
        .expect("matching shapes");

    let closure = buchberger(
        &returned
            .identities
            .iter()
            .map(|identity| identity.polynomial.clone())
            .collect::<Vec<_>>(),
    )
    .expect("closure");
    let (remainder, _) = normal_form(&sine_law, &closure.basis).expect("reduction runs");
    assert!(
        remainder.is_zero(),
        "the sine addition law lies in the certified ideal; remainder {}",
        remainder.written(&names)
    );

    // I4's reduction: strictly fewer elementary generators than certified identities, and every
    // certified identity reduces to zero modulo the ideal the generators generate. That second
    // half is bounded-degree completeness; the all-degree obligation stays named.
    let elementary = elementary_generators(&returned.identities).expect("the reduction runs");
    assert!(
        elementary.generators.len() < returned.identities.len(),
        "some certified identity must be an ideal consequence of the others: {} of {}",
        elementary.generators.len(),
        returned.identities.len()
    );
    assert!(elementary.consequences >= 1);
    let completeness = bounded_degree_completeness(&returned.identities, &elementary.closure)
        .expect("the reduction runs");
    assert!(
        completeness.every_certified_vector_reduces_to_zero,
        "unreduced modulo the elementary generators: {:?}",
        completeness.unreduced
    );
}

#[test]
fn a_single_chart_wrongly_certifies_the_galilean_collapse() {
    // The k = 0 fibre of the two-sided circle is C² = 1, two components. The principal winding
    // covers only C = +1, and on that chart alone C − 1 substitutes to the zero polynomial.
    let principal = collapsed_addition(0, &[(1, 1)], 2).expect("the one-chart Galilean declares");
    let complete = collapsed_addition(0, &[(1, 1), (1, -1), (-1, 1), (-1, -1)], 2)
        .expect("the four-chart Galilean declares");

    let names = named(&COLLAPSED_ADDITION_RECEIVERS);
    let width = COLLAPSED_ADDITION_RECEIVERS.len();
    let index = |name: &str| {
        names
            .iter()
            .position(|slot| slot == name)
            .expect("a receiver")
    };
    let mut exponents = vec![0u32; width];
    exponents[index("C1")] = 1;
    let candidate = ExactMultivariate::term(width, exponents, Rat::one())
        .expect("a term")
        .minus(&ExactMultivariate::constant(width, Rat::one()))
        .expect("matching shapes");

    let vector_of = |configuration: &Configuration, polynomial: &ExactMultivariate| {
        configuration
            .family()
            .monomials()
            .iter()
            .map(|monomial| {
                polynomial
                    .terms()
                    .get(monomial)
                    .cloned()
                    .unwrap_or_else(Rat::zero)
            })
            .collect::<Vec<_>>()
    };

    let grid = principal.candidate_points(64);
    let on_one_chart =
        certify(&principal, &vector_of(&principal, &candidate), &grid).expect("certification runs");
    assert!(
        on_one_chart.is_ok(),
        "the principal winding alone certifies C1 - 1 — this is the coverage failure the contract \
         names, and it is reproduced here rather than assumed away"
    );

    let on_all_charts =
        certify(&complete, &vector_of(&complete, &candidate), &grid).expect("certification runs");
    let refused = on_all_charts.expect_err("the four-winding chart family refuses C1 - 1");
    let counterexample = refused.verdicts.iter().find_map(|verdict| match verdict {
        ChartVerdict::Refused {
            counterexample: Some(point),
            value: Some(value),
            chart,
            ..
        } => Some((chart.clone(), point.clone(), value.clone())),
        _ => None,
    });
    let (chart, point, value) = counterexample.expect("a refusal returns an admissible point");
    assert!(
        chart.contains("-1"),
        "the half-turn winding is what sees the second component: {chart}"
    );
    assert!(
        !value.is_zero(),
        "the counterexample point {point:?} gives a nonzero value"
    );
}

#[test]
fn the_galilean_collapse_creates_relations_only_when_a_component_is_missed() {
    let generic = two_sided_addition(2, 1).expect("T1 declares");
    let generic_return = walk(&generic).expect("T1 walks");
    let assignment: Vec<Option<Rat>> = vec![None, None, None, None, None, None, Some(Rat::zero())];
    let retained = [0usize, 1, 2, 3, 4, 5];

    let complete = collapsed_addition(0, &[(1, 1), (1, -1), (-1, 1), (-1, -1)], 2)
        .expect("the four-chart Galilean declares");
    let complete_return = walk(&complete).expect("the four-chart Galilean walks");
    let full = compare_collapse(
        "k -> 0 with all four windings",
        &generic_return.identities,
        &assignment,
        &retained,
        &complete_return,
    )
    .expect("the comparison runs");
    assert!(
        full.specialized_lies_in_transported,
        "with every component covered the specialized kernel is the transported ideal; extras: {:?}",
        full.extra_relations
            .iter()
            .map(|relation| relation.written(&named(&COLLAPSED_ADDITION_RECEIVERS)))
            .collect::<Vec<_>>()
    );

    let principal = collapsed_addition(0, &[(1, 1)], 2).expect("the one-chart Galilean declares");
    let principal_return = walk(&principal).expect("the one-chart Galilean walks");
    let partial = compare_collapse(
        "k -> 0 with the principal winding alone",
        &generic_return.identities,
        &assignment,
        &retained,
        &principal_return,
    )
    .expect("the comparison runs");
    assert!(
        !partial.specialized_lies_in_transported,
        "the principal winding's own configuration has strictly more identities"
    );
    assert!(
        principal_return.identities.len() > complete_return.identities.len(),
        "{} against {}",
        principal_return.identities.len(),
        complete_return.identities.len()
    );
}

#[test]
fn the_circular_and_hyperbolic_collapses_add_nothing() {
    let generic = two_sided_addition(2, 1).expect("T1 declares");
    let generic_return = walk(&generic).expect("T1 walks");
    let retained = [0usize, 1, 2, 3, 4, 5];
    for curvature in [1i64, -1] {
        let assignment: Vec<Option<Rat>> = vec![
            None,
            None,
            None,
            None,
            None,
            None,
            Some(rational(curvature)),
        ];
        let collapsed = collapsed_addition(curvature, &[(1, 1), (1, -1), (-1, 1), (-1, -1)], 2)
            .expect("the collapse declares");
        let collapsed_return = walk(&collapsed).expect("the collapse walks");
        let comparison = compare_collapse(
            &format!("k -> {curvature}"),
            &generic_return.identities,
            &assignment,
            &retained,
            &collapsed_return,
        )
        .expect("the comparison runs");
        assert!(
            comparison.specialized_lies_in_transported,
            "k = {curvature} creates {:?}",
            comparison
                .extra_relations
                .iter()
                .map(|relation| relation.written(&named(&COLLAPSED_ADDITION_RECEIVERS)))
                .collect::<Vec<_>>()
        );
    }
}

/// The two transferred relations as polynomials in the ten constant-curvature receivers, built by
/// hand so the certified ideal can be asked whether it contains them.
fn transferred_laws(
    curvature: i64,
) -> Result<(ExactMultivariate, ExactMultivariate), IdentityAtlasError> {
    let width = HELICAL_RECEIVERS_AT.len();
    let slot = |name: &str| {
        HELICAL_RECEIVERS_AT
            .iter()
            .position(|receiver| *receiver == name)
            .expect("a declared receiver")
    };
    let monomial = |factors: &[&str], coefficient: i64| {
        let mut exponents = vec![0u32; width];
        for factor in factors {
            exponents[slot(factor)] += 1;
        }
        ExactMultivariate::term(width, exponents, rational(coefficient)).expect("a term")
    };
    // 1-part: SpQ12K SpQ13K + k SpQ12R SpQ13R - CrossK^2 - k CrossR^2 - Qua1 GramK - k Pit1 GramR
    let killing = monomial(&["SpQ12K", "SpQ13K"], 1)
        .plus(&monomial(&["SpQ12R", "SpQ13R"], curvature))?
        .minus(&monomial(&["CrossK", "CrossK"], 1))?
        .minus(&monomial(&["CrossR", "CrossR"], curvature))?
        .minus(&monomial(&["Qua1", "GramK"], 1))?
        .minus(&monomial(&["Pit1", "GramR"], curvature))?;
    // iota-part: SpQ12K SpQ13R + SpQ12R SpQ13K - 2 CrossK CrossR - Qua1 GramR - Pit1 GramK
    let reciprocal = monomial(&["SpQ12K", "SpQ13R"], 1)
        .plus(&monomial(&["SpQ12R", "SpQ13K"], 1))?
        .minus(&monomial(&["CrossK", "CrossR"], 2))?
        .minus(&monomial(&["Qua1", "GramR"], 1))?
        .minus(&monomial(&["Pit1", "GramK"], 1))?;
    Ok((killing, reciprocal))
}

#[test]
fn the_transferred_laws_of_the_helical_triple_are_certified_and_hold_on_real_screws() {
    // One walk, three questions. The `k = 0` instance is the Euclidean screw case — dual numbers,
    // Study's spatial law for three lines — and is the smallest declared family that carries both
    // components of the transfer.
    let names = named(&HELICAL_RECEIVERS_AT);
    for curvature in [0i64, 1, -1] {
        let configuration = helical_triple_at(curvature, 2).expect("T2 declares");
        let returned = walk(&configuration).expect("T2 walks");
        assert!(returned.refusals.is_empty(), "no candidate stays refused");
        assert!(
            returned.identities.len() >= 2,
            "at k = {curvature} the transfer has two components: {:?}",
            returned
                .identities
                .iter()
                .map(|identity| identity.polynomial.written(&names))
                .collect::<Vec<_>>()
        );

        // Both hand-built relations lie in the certified ideal, which is what "the transferred law
        // of cosines and the transferred law of sines were recovered" means.
        let closure = buchberger(
            &returned
                .identities
                .iter()
                .map(|identity| identity.polynomial.clone())
                .collect::<Vec<_>>(),
        )
        .expect("closure");
        let (killing, reciprocal) = transferred_laws(curvature).expect("laws build");
        for (law, label) in [(killing, "Killing part"), (reciprocal, "reciprocal part")] {
            let (remainder, _) = normal_form(&law, &closure.basis).expect("reduction runs");
            assert!(
                remainder.is_zero(),
                "the {label} at k = {curvature} is not in the certified ideal; remainder {}",
                remainder.written(&names)
            );
        }

        // Soundness needs no coverage hypothesis at all: the receivers of actual helical axes —
        // three rational directions with rational moments — lie in the certified zero set.
        let screw = |u: [i64; 3], v: [i64; 3]| {
            (
                [rational(u[0]), rational(u[1]), rational(u[2])],
                [rational(v[0]), rational(v[1]), rational(v[2])],
            )
        };
        let screws = [
            screw([3, 4, 0], [1, -2, 5]),
            screw([0, 5, 12], [-3, 1, 2]),
            screw([8, -1, 4], [2, 7, -1]),
        ];
        let point = screw_gram_point(&screws, rational(curvature));
        let receivers = configuration.charts()[0]
            .receivers_at(&point[..12])
            .expect("the polynomial chart never refuses");
        for identity in &returned.identities {
            let mut total = Rat::zero();
            for (monomial, coefficient) in identity.polynomial.terms() {
                let mut term = coefficient.clone();
                for (slot, exponent) in monomial.iter().enumerate() {
                    for _ in 0..*exponent {
                        term *= &receivers[slot];
                    }
                }
                total += term;
            }
            assert!(
                total.is_zero(),
                "a real screw triple at k = {curvature} violated a certified identity: {}",
                identity.polynomial.written(&names)
            );
        }
    }
}

/// The uniform-in-`k` helical triple: the widest declared family in this module at 132 columns, and
/// the one whose exact rational reduction is the measured cost.
#[test]
fn the_transferred_laws_are_recovered_uniformly_in_the_curvature() {
    let configuration = helical_triple(2, 1).expect("T2 declares");
    let returned = walk(&configuration).expect("T2 walks");
    assert!(returned.refusals.is_empty());
    let names = named(&HELICAL_RECEIVERS);
    let written: Vec<String> = returned
        .identities
        .iter()
        .map(|identity| identity.polynomial.written(&names))
        .collect();
    assert!(returned.identities.len() >= 2, "{written:?}");
    let carries = |needle: &str| written.iter().any(|identity| identity.contains(needle));
    assert!(
        carries("Pit1"),
        "the reciprocal law carries the pitch: {written:?}"
    );
    assert!(
        carries("Curv"),
        "the Killing law is uniform in k: {written:?}"
    );
}

#[test]
fn the_column_matroid_is_read_at_its_owners_supported_scope() {
    let configuration = two_sided_angle(2, 1).expect("T0 declares");
    let returned = walk(&configuration).expect("T0 walks");
    let points: Vec<(usize, Vec<Rat>)> = configuration
        .candidate_points(96)
        .into_iter()
        .enumerate()
        .filter_map(|(index, point)| {
            let chart = index % configuration.charts().len();
            configuration.charts()[chart]
                .denominator()
                .evaluate(&point)
                .ok()
                .filter(|value| !value.is_zero())
                .map(|_| (chart, point))
        })
        .take(48)
        .collect();
    let reading = read_column_matroid(&configuration, &points, &returned.identities)
        .expect("the matroid reads");
    assert_eq!(reading.ground, configuration.family().monomials().len());
    assert_eq!(
        reading.identity_supports.len(),
        returned.identities.len(),
        "one support per certified identity"
    );
    assert!(
        reading.support_is_circuit.iter().all(|circuit| *circuit),
        "the support of a certified identity is a minimal sampled dependency"
    );
    match &reading.chow {
        ChowScope::Admitted { ground, rank, .. } => {
            assert_eq!(*ground, 3, "C^2 + k S^2 - 1 has a three-column circuit");
            assert_eq!(*rank, 2, "whose matroid is U(2, 3)");
        }
        ChowScope::Refused { reason } => panic!("the three-column circuit is admissible: {reason}"),
    }
    match &reading.full_matroid_scope {
        ChowScope::Refused { reason } => assert!(
            reason.contains("2^|E|"),
            "the whole-matroid refusal names the owner's presentation: {reason}"
        ),
        ChowScope::Admitted { ground, .. } => assert!(
            *ground <= CHOW_GROUND_CEILING,
            "a wide column matroid must be refused, not admitted"
        ),
    }
}

#[test]
fn a_wide_family_is_refused_by_the_chow_owner_rather_than_mis_presented() {
    let configuration = two_sided_addition(2, 1).expect("T1 declares");
    let points: Vec<(usize, Vec<Rat>)> = configuration
        .candidate_points(64)
        .into_iter()
        .enumerate()
        .filter_map(|(index, point)| {
            let chart = index % configuration.charts().len();
            configuration.charts()[chart]
                .denominator()
                .evaluate(&point)
                .ok()
                .filter(|value| !value.is_zero())
                .map(|_| (chart, point))
        })
        .take(24)
        .collect();
    let reading = read_column_matroid(&configuration, &points, &[]).expect("the matroid reads");
    assert!(
        reading.ground > CHOW_GROUND_CEILING,
        "the T1 family is wide on purpose"
    );
    match &reading.full_matroid_scope {
        ChowScope::Refused { reason } => {
            assert!(
                reason.contains("2^|E|"),
                "the refusal names the owner's presentation: {reason}"
            );
        }
        ChowScope::Admitted { .. } => panic!("a 56-column matroid is not admissible at that scope"),
    }
    assert!(
        matches!(reading.chow, ChowScope::Refused { .. }),
        "with no certified identity supplied there is no identity circuit to read"
    );
}

#[test]
fn a_groebner_basis_of_a_smaller_ideal_does_not_claim_the_larger_one() {
    // {x} is already a Gröbner basis and does not generate <x, y>: the contract's own example,
    // made a test so the closure type cannot be read as an all-degree completeness claim.
    let x = ExactMultivariate::variable(2, 0).expect("x");
    let y = ExactMultivariate::variable(2, 1).expect("y");
    let closure = buchberger(&[x.clone()]).expect("a singleton completes");
    assert_eq!(closure.basis.len(), 1);
    let (remainder, _) = normal_form(&y, &closure.basis).expect("reduction runs");
    assert!(
        !remainder.is_zero(),
        "y does not reduce to zero modulo {{x}}, so the closure certifies nothing about <x, y>"
    );
}

#[test]
fn a_refusal_is_typed_and_never_a_panic() {
    let chart = RationalChart::polynomial(
        "line",
        &["x"],
        vec![ExactMultivariate::variable(1, 0).expect("x")],
    )
    .expect("a chart");
    let family = ReceiverFamily::total_degree(&["a", "b"], 1).expect("two receivers");
    let refusal = Configuration::new("mismatched", family, vec![chart], "none", 3, 1);
    assert!(matches!(
        refusal,
        Err(IdentityAtlasError::ChartWidthMismatch { .. })
    ));

    let family = ReceiverFamily::total_degree(&["a"], 1).expect("one receiver");
    let empty = Configuration::new("chartless", family, Vec::new(), "none", 3, 1);
    assert!(matches!(empty, Err(IdentityAtlasError::NoChart { .. })));

    let divisor = ExactMultivariate::from_integer_terms(1, &[(&[1], 1)]).expect("x");
    let chart = RationalChart::new(
        "punctured",
        &["x"],
        vec![ExactMultivariate::constant(1, Rat::one())],
        divisor,
        "x != 0",
    )
    .expect("a chart");
    assert!(matches!(
        chart.receivers_at(&[Rat::zero()]),
        Err(IdentityAtlasError::DenominatorVanishes { .. })
    ));

    let zero_denominator = RationalChart::new(
        "zero denominator",
        &["x"],
        vec![ExactMultivariate::constant(1, Rat::one())],
        ExactMultivariate::zero(1),
        "x != 0",
    );
    assert!(matches!(
        zero_denominator,
        Err(IdentityAtlasError::ZeroChartDenominator { .. })
    ));

    let mismatched_numerator = RationalChart::new(
        "mismatched numerator",
        &["x"],
        vec![ExactMultivariate::variable(2, 0).expect("two-variable numerator")],
        ExactMultivariate::constant(1, Rat::one()),
        "all x",
    );
    assert!(matches!(
        mismatched_numerator,
        Err(IdentityAtlasError::ChartVariableCountMismatch { .. })
    ));

    let line = Configuration::new(
        "line",
        ReceiverFamily::total_degree(&["a"], 1).expect("family"),
        vec![
            RationalChart::polynomial(
                "line",
                &["x"],
                vec![ExactMultivariate::variable(1, 0).expect("x")],
            )
            .expect("chart"),
        ],
        "the supplied line chart",
        3,
        1,
    )
    .expect("line");
    assert!(matches!(
        evaluation_matrix(&line, &[(1, vec![Rat::zero()])]),
        Err(IdentityAtlasError::ChartIndex { .. })
    ));
    assert!(matches!(
        Configuration::new(
            "invalid span",
            ReceiverFamily::total_degree(&["a"], 1).expect("family"),
            line.charts().to_vec(),
            "line",
            0,
            1,
        ),
        Err(IdentityAtlasError::InvalidGridSpan { .. })
    ));
    assert!(matches!(
        Configuration::new(
            "overflow span",
            ReceiverFamily::total_degree(&["a"], 1).expect("family"),
            line.charts().to_vec(),
            "line",
            i64::MAX,
            1,
        ),
        Err(IdentityAtlasError::GridSpanOverflow { .. })
    ));
}

#[test]
fn unresolved_grid_refusal_is_typed_instead_of_returning_a_partial_atlas() {
    let family = ReceiverFamily::total_degree(&["a"], 1).expect("family");
    let a =
        ExactMultivariate::from_integer_terms(1, &[(&[3], 1), (&[1], -1)]).expect("a(t) = t^3 - t");
    let chart = RationalChart::polynomial("three-root chart", &["t"], vec![a]).expect("chart");
    let configuration = Configuration::new(
        "all candidate points are roots",
        family,
        vec![chart],
        "the supplied polynomial chart",
        1,
        1,
    )
    .expect("configuration");
    assert!(matches!(
        walk(&configuration),
        Err(IdentityAtlasError::UnresolvedCertification { .. })
    ));
}

#[test]
fn polynomial_arithmetic_refuses_shape_and_exponent_overflow() {
    let one_variable = ExactMultivariate::variable(1, 0).expect("one variable");
    let two_variables = ExactMultivariate::variable(2, 0).expect("two variables");
    assert!(matches!(
        one_variable.plus(&two_variables),
        Err(IdentityAtlasError::PolynomialShapeMismatch { .. })
    ));
    assert!(matches!(
        one_variable.times(&two_variables),
        Err(IdentityAtlasError::PolynomialShapeMismatch { .. })
    ));

    let huge = ExactMultivariate::term(1, vec![u32::MAX], Rat::one()).expect("huge exponent");
    assert_eq!(
        huge.evaluate(&[Rat::one()]).expect("exact rational power"),
        Rat::one()
    );
    assert!(matches!(
        huge.times(&one_variable),
        Err(IdentityAtlasError::ExponentOverflow { .. })
    ));
    assert!(matches!(
        huge.powered(2),
        Err(IdentityAtlasError::ExponentOverflow { .. })
    ));
    assert_eq!(
        ExactMultivariate::constant(1, Rat::one())
            .powered(u32::MAX)
            .expect("checked exponentiation by squaring")
            .evaluate(&[Rat::zero()])
            .expect("constant evaluates"),
        Rat::one()
    );
    assert!(matches!(
        ExactMultivariate::term(2, vec![u32::MAX, u32::MAX], Rat::one()),
        Err(IdentityAtlasError::TotalDegreeOverflow)
    ));
}

#[test]
fn a_parallel_column_is_refused_by_the_simple_chow_scope() {
    let family = ReceiverFamily::total_degree(&["a", "b"], 1).expect("family");
    let chart = RationalChart::polynomial(
        "duplicated receivers",
        &["x"],
        vec![
            ExactMultivariate::variable(1, 0).expect("a"),
            ExactMultivariate::variable(1, 0).expect("b"),
        ],
    )
    .expect("chart");
    let configuration = Configuration::new(
        "parallel columns",
        family,
        vec![chart],
        "the supplied duplicated-receiver chart",
        3,
        1,
    )
    .expect("configuration");
    let reading = read_column_matroid(&configuration, &[(0, vec![rational(2)])], &[])
        .expect("matroid reading");
    assert_eq!(reading.parallel_classes.len(), 1);
    assert!(matches!(
        reading.full_matroid_scope,
        ChowScope::Refused { .. }
    ));
}

#[test]
fn no_float_reaches_a_carrying_path() {
    let source = include_str!("../identity_atlas.rs");
    for line in source.lines() {
        assert!(
            !line.contains(" f32") && !line.contains(" f64"),
            "a float reached the atlas: {line}"
        );
    }
}
