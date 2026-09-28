use super::{PopulationReceivingFaceHealthError, population_receiving_face_health};
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{Rat, integer, rat};
use crate::receiver::population::sampling::CertifiedClass;
use crate::receiver::population::tests::Fixed;
use crate::receiver::population::{Family, Population};

fn q(numerator: i64, denominator: i64) -> Rat {
    rat(numerator, denominator)
}

fn posterior() -> Vec<ExactInterval> {
    vec![
        ExactInterval::new(q(1, 4), q(1, 2)).unwrap(),
        ExactInterval::new(q(1, 2), q(3, 4)).unwrap(),
    ]
}

fn family_class_faces() -> Vec<Vec<Rat>> {
    vec![vec![integer(1), integer(0)], vec![integer(0), integer(1)]]
}

#[test]
fn exact_family_widths_bound_two_family_mixture_variation() {
    let class_face = vec![
        ExactInterval::new(q(1, 4), q(1, 2)).unwrap(),
        ExactInterval::new(q(1, 2), q(3, 4)).unwrap(),
    ];
    let draws = vec![
        CertifiedClass {
            class: 0,
            prior_upper: q(0, 1),
            through_lower: q(1, 4),
        },
        CertifiedClass {
            class: 1,
            prior_upper: q(1, 2),
            through_lower: q(1, 1),
        },
    ];

    let receipt =
        population_receiving_face_health(&posterior(), &family_class_faces(), &class_face, &draws)
            .unwrap();

    assert_eq!(receipt.family_posterior_l1_variation_bound, q(1, 2));
    assert_eq!(receipt.family_to_class_l1_operator_bound, q(1, 1));
    assert_eq!(receipt.family_to_class_nonexpansive_factor, q(1, 1));
    assert_eq!(receipt.certified_draw_decision_count, 2);
}

#[test]
fn simplex_covering_class_face_is_refused() {
    let full_simplex = vec![
        ExactInterval::new(q(0, 1), q(1, 1)).unwrap(),
        ExactInterval::new(q(0, 1), q(1, 1)).unwrap(),
    ];

    let error =
        population_receiving_face_health(&posterior(), &family_class_faces(), &full_simplex, &[])
            .unwrap_err();

    assert_eq!(
        error,
        PopulationReceivingFaceHealthError::SimplexCoveringClassFace
    );
}

#[test]
fn actual_population_health_keeps_a_dead_family_at_zero_mass() {
    let mut population = Population::new(vec![
        Box::new(Fixed::new(vec![integer(1), integer(0)], 1)) as Box<dyn Family>,
        Box::new(Fixed::new(vec![integer(0), integer(1)], 1)) as Box<dyn Family>,
    ])
    .unwrap();
    population.receive(0).unwrap();
    let health = population.receiving_face_health().unwrap();
    assert_eq!(health.family_posterior_l1_variation_bound, integer(0));
    assert_eq!(health.family_to_class_l1_operator_bound, integer(1));
}
