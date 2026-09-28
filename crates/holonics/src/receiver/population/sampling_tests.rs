use super::sampling::{SamplingError, select_class};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}

#[test]
fn point_face_selects_the_inverse_cdf_class_with_exact_bounds() {
    let face = vec![
        ExactInterval::point(q(1, 4)),
        ExactInterval::point(q(1, 2)),
        ExactInterval::point(q(1, 4)),
    ];
    let selected = select_class(&face, &q(1, 4)).unwrap();
    assert_eq!(selected.class, 1);
    assert_eq!(selected.prior_upper, q(1, 4));
    assert_eq!(selected.through_lower, q(3, 4));
}

#[test]
fn overlapping_face_refuses_and_returns_exact_crossing_bounds() {
    let face = vec![
        ExactInterval::new(q(0, 1), q(3, 4)).unwrap(),
        ExactInterval::new(q(1, 4), q(1, 1)).unwrap(),
    ];
    let error = select_class(&face, &q(1, 2)).unwrap_err();
    let SamplingError::UnresolvedFibre { draw, crossings } = error else {
        panic!("expected unresolved fibre refusal")
    };
    assert_eq!(draw, q(1, 2));
    assert_eq!(crossings.len(), 2);
    assert_eq!(crossings[0].class, 0);
    assert_eq!(crossings[0].prior_upper, q(0, 1));
    assert_eq!(crossings[0].through_lower, q(0, 1));
}

#[test]
fn invalid_normalization_is_refused() {
    let face = vec![ExactInterval::point(q(1, 4)), ExactInterval::point(q(1, 4))];
    assert!(matches!(
        select_class(&face, &q(1, 8)),
        Err(SamplingError::InvalidNormalization { lower_total, upper_total })
            if lower_total == q(1, 2) && upper_total == q(1, 2)
    ));
}

#[test]
fn stop_class_is_selectable_in_a_268_class_chart() {
    let mut face = vec![ExactInterval::point(q(0, 1)); 268];
    face[267] = ExactInterval::point(q(1, 1));
    let selected = select_class(&face, &q(999, 1000)).unwrap();
    assert_eq!(selected.class, 267);
    assert_eq!(selected.prior_upper, q(0, 1));
    assert_eq!(selected.through_lower, q(1, 1));
}
