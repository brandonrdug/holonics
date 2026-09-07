//! CUDA-only enclosed-junction controls.
//!
//! The parent module includes this file explicitly.  These tests compare the enclosed dyadic
//! face with the independently founded exact-word body and use the cold exact decoder only as a
//! receiver reference.  No host value is supplied to native conduct.

use super::super::super::super::*;
use super::{NativeFieldCurrentBall, NativeFieldEnclosedJunctionReading};
use crate::dimensional_wave::ExactComplexWaveCurrent;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::ResidentGrain;
use num_rational::BigRational as Rat;
use num_traits::Zero;

fn phase(real: i64, imaginary: i64, denominator: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, denominator).unwrap()
}

fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    (0..nodes)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}

fn source_vector(step: &NativeFieldStep) -> Vec<ExactComplexWaveCurrent> {
    step.outgoing
        .iter()
        .zip(&step.held_successor)
        .flat_map(|(outgoing, held)| [outgoing.clone(), held.clone()])
        .collect()
}

fn append_target(
    mut source: Vec<ExactComplexWaveCurrent>,
    nodes: usize,
) -> Vec<ExactComplexWaveCurrent> {
    source.extend(std::iter::repeat_with(ExactComplexWaveCurrent::zero).take(nodes));
    source
}

fn twice(values: &[ExactComplexWaveCurrent]) -> Vec<ExactComplexWaveCurrent> {
    values
        .iter()
        .map(|value| value.scaled(&Rat::from_integer(2.into())))
        .collect()
}

fn assert_ball_contains(ball: &NativeFieldCurrentBall, exact: &[ExactComplexWaveCurrent]) {
    assert!(
        ball.contains(exact),
        "exact value escaped enclosed current ball"
    );
}

fn root_ball(ball: &NativeFieldCurrentBall, nodes: usize) -> NativeFieldCurrentBall {
    NativeFieldCurrentBall {
        center: ball.center[2 * nodes..].to_vec(),
        radius: ball.radius.clone(),
    }
}

fn squared_distance(left: &[ExactComplexWaveCurrent], right: &[ExactComplexWaveCurrent]) -> Rat {
    left.iter()
        .zip(right)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum()
}

fn assert_enclosed_matches_exact(
    enclosed: &NativeFieldEnclosedJunctionReading,
    exact: &NativeFieldExactJunctionReading,
) {
    assert_ball_contains(&enclosed.potential, &exact.potential);
    assert_ball_contains(&enclosed.outgoing, &exact.outgoing);
    assert_ball_contains(&enclosed.held_current, &exact.held_current);
    assert_ball_contains(&enclosed.potential_prefix, &exact.potential_prefix);
}

#[test]
#[ignore = "requires CUDA; C=0 first unlinked enclosed report at fractional bits 72"]
fn enclosed_first_unlinked_unit_input_has_zero_radius_and_full_packed_shape() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 1;
    let grain = ResidentGrain(72);
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(nodes), grain)
            .unwrap();
    let step = body
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 1)]))
        .unwrap();
    let reading = step.junction.as_ref().unwrap().enclosed().unwrap();
    let unit_source = append_target(source_vector(&step), nodes);
    assert_eq!(reading.source_center, unit_source);
    assert_eq!(reading.potential.center, twice(&unit_source));
    assert_eq!(reading.outgoing.center, unit_source);
    assert!(reading
        .held_current
        .center
        .iter()
        .all(ExactComplexWaveCurrent::is_zero));
    assert_eq!(reading.potential_prefix.center, twice(&unit_source));
    assert_eq!(reading.potential.radius, Rat::zero());
    assert_eq!(reading.outgoing.radius, Rat::zero());
    assert_eq!(reading.held_current.radius, Rat::zero());
    assert_eq!(reading.potential_prefix.radius, Rat::zero());
    assert_eq!(reading.source_error_l1_bound, Rat::zero());
    assert!(reading
        .solve_residual
        .iter()
        .all(ExactComplexWaveCurrent::is_zero));

    let packed = body.inspect_junction(0).unwrap().unwrap();
    let dimension = 6 * nodes;
    assert_eq!(packed.rows, 1);
    assert_eq!(packed.width, 12 * (dimension + 1));
}

#[test]
#[ignore = "requires CUDA; exact-word and enclosed bodies share native state and enclosed source error"]
fn enclosed_small_rational_inputs_contain_exact_native_faces_and_retain_c() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 2;
    let grain = ResidentGrain(72);
    let mut exact =
        NativeConstitutiveField::found_with_paired_junction(&surface, seed(nodes)).unwrap();
    let mut enclosed =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(nodes), grain)
            .unwrap();
    let first_input = vec![phase(1, 0, 7), phase(2, 1, 7)];
    let exact_first = exact
        .advance(&mut NativeFieldOccurrence::entering(first_input.clone()))
        .unwrap();
    let enclosed_first = enclosed
        .advance(&mut NativeFieldOccurrence::entering(first_input))
        .unwrap();
    let later = vec![phase(3, -1, 7), phase(-2, 1, 7)];
    let mut contact = source_vector(&exact_first);
    contact.extend(later.iter().map(|a| a.current().negated()));
    let prefix_before = exact_first
        .junction
        .as_ref()
        .unwrap()
        .exact()
        .unwrap()
        .potential_prefix
        .clone();
    // At this full two-node rational chart the old integer-adjugate path exhausts its
    // intermediate carrier. The enclosed operation must still carry the same exact solution.
    assert!(matches!(
        exact.advance(&mut NativeFieldOccurrence::through(
            exact_first.source,
            later.clone()
        )),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    let enclosed_second = enclosed
        .advance(&mut NativeFieldOccurrence::through(
            enclosed_first.source,
            later,
        ))
        .unwrap();
    let reading = enclosed_second
        .junction
        .as_ref()
        .unwrap()
        .enclosed()
        .unwrap();
    let u = append_target(source_vector(&enclosed_second), nodes);
    let projection = contact
        .iter()
        .zip(&u)
        .fold(ExactComplexWaveCurrent::zero(), |sum, (d, u)| {
            sum.add(&d.conjugate().multiply(u))
        });
    let norm = contact
        .iter()
        .map(ExactComplexWaveCurrent::norm_square)
        .sum::<Rat>();
    let coefficient =
        projection.scaled(&(Rat::from_integer(1.into()) / (Rat::from_integer(1.into()) + norm)));
    let two = Rat::from_integer(2.into());
    // Independent rank-one inverse: (I+d d*)^-1 u = u-d(d*u)/(1+d*d).
    let v: Vec<_> = u
        .iter()
        .zip(&contact)
        .map(|(u, d)| u.subtract(&d.multiply(&coefficient)).scaled(&two))
        .collect();
    let exact_face = NativeFieldExactJunctionReading {
        outgoing: v.iter().zip(&u).map(|(v, u)| v.subtract(u)).collect(),
        held_current: u
            .iter()
            .zip(&v)
            .map(|(u, v)| u.scaled(&two).subtract(v))
            .collect(),
        potential_prefix: prefix_before
            .iter()
            .zip(&v)
            .map(|(p, v)| p.subtract(v))
            .collect(),
        potential: v,
    };
    assert_enclosed_matches_exact(reading, &exact_face);
    assert!(reading.source_error_l1_bound > Rat::zero());
    assert_eq!(
        enclosed.inspect_exact_junction(1).unwrap().unwrap(),
        exact_face
    );
}

#[test]
#[ignore = "requires CUDA; delayed source birth uses exact residual trace and enclosed current balls"]
fn enclosed_delayed_handle_decodes_exact_junction_and_internal_current() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 1;
    let mut exact =
        NativeConstitutiveField::found_with_paired_junction(&surface, seed(nodes)).unwrap();
    let mut enclosed = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed(nodes),
        ResidentGrain(72),
    )
    .unwrap();
    let exact_first = exact
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 7)]))
        .unwrap();
    let enclosed_first = enclosed
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 7)]))
        .unwrap();
    drop(
        exact
            .advance(&mut NativeFieldOccurrence::entering(vec![phase(2, 1, 7)]))
            .unwrap()
            .source,
    );
    drop(
        enclosed
            .advance(&mut NativeFieldOccurrence::entering(vec![phase(2, 1, 7)]))
            .unwrap()
            .source,
    );
    let exact_delayed = exact
        .advance(&mut NativeFieldOccurrence::through(
            exact_first.source,
            vec![phase(-1, 3, 7)],
        ))
        .unwrap();
    let enclosed_delayed = enclosed
        .advance(&mut NativeFieldOccurrence::through(
            enclosed_first.source,
            vec![phase(-1, 3, 7)],
        ))
        .unwrap();
    let exact_reading = exact_delayed.junction.as_ref().unwrap().exact().unwrap();
    assert_enclosed_matches_exact(
        enclosed_delayed
            .junction
            .as_ref()
            .unwrap()
            .enclosed()
            .unwrap(),
        exact_reading,
    );
    let cold_exact = enclosed.inspect_exact_junction(2).unwrap().unwrap();
    assert_eq!(cold_exact.potential, exact_reading.potential);
    assert_eq!(cold_exact.outgoing, exact_reading.outgoing);
    assert_eq!(cold_exact.held_current, exact_reading.held_current);
    assert_eq!(cold_exact.potential_prefix, exact_reading.potential_prefix);
    let exact_internal = exact.inspect_internal_currents().unwrap().unwrap();
    let enclosed_internal = enclosed.inspect_internal_currents().unwrap().unwrap();
    assert_eq!(exact_internal.len(), enclosed_internal.len());
    for (left, right) in exact_internal.iter().zip(&enclosed_internal) {
        assert_eq!(left.source_occurrence, right.source_occurrence);
        assert_eq!(left.receiving_occurrence, right.receiving_occurrence);
        assert_eq!(left.current, right.current);
    }
    let balls = enclosed
        .inspect_internal_current_enclosures()
        .unwrap()
        .unwrap();
    for (exact_current, ball) in exact_internal.iter().zip(&balls) {
        assert!(ball.current.contains(&[exact_current.current.clone()]));
    }
}

#[test]
#[ignore = "requires CUDA; equal C and aligned raw branches still retain divergent history context"]
fn enclosed_equal_c_history_context_produces_disjoint_final_target_balls() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 1;
    let mut left = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed(nodes),
        ResidentGrain(72),
    )
    .unwrap();
    let mut right = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed(nodes),
        ResidentGrain(72),
    )
    .unwrap();
    let left_first = left
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 1)]))
        .unwrap();
    let right_first = right
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 1)]))
        .unwrap();
    drop(
        left.advance(&mut NativeFieldOccurrence::through(
            left_first.source,
            vec![phase(1, 0, 1)],
        ))
        .unwrap()
        .source,
    );
    drop(
        right
            .advance(&mut NativeFieldOccurrence::through(
                right_first.source,
                vec![phase(1, 0, 1)],
            ))
            .unwrap()
            .source,
    );
    for (a, b) in [
        (phase(2, 1, 1), phase(-2, 1, 1)),
        (phase(1, -2, 1), phase(2, -1, 1)),
    ] {
        drop(
            left.advance(&mut NativeFieldOccurrence::entering(vec![a]))
                .unwrap()
                .source,
        );
        drop(
            right
                .advance(&mut NativeFieldOccurrence::entering(vec![b]))
                .unwrap()
                .source,
        );
    }
    for input in [phase(2, 3, 1), phase(-1, 4, 1)] {
        drop(
            left.advance(&mut NativeFieldOccurrence::entering(vec![input]))
                .unwrap()
                .source,
        );
        drop(
            right
                .advance(&mut NativeFieldOccurrence::entering(vec![input]))
                .unwrap()
                .source,
        );
    }
    let left_step = left
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(3, -2, 1)]))
        .unwrap();
    let right_step = right
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(3, -2, 1)]))
        .unwrap();
    assert_eq!(
        left.inspect_junction_covariance().unwrap(),
        right.inspect_junction_covariance().unwrap()
    );
    let left_reading = left_step.junction.as_ref().unwrap().enclosed().unwrap();
    let right_reading = right_step.junction.as_ref().unwrap().enclosed().unwrap();
    assert_eq!(left_reading.source_center, right_reading.source_center);
    assert_eq!(
        left_reading.source_error_l1_bound,
        right_reading.source_error_l1_bound
    );
    let left_target = root_ball(&left_reading.outgoing, nodes);
    let right_target = root_ball(&right_reading.outgoing, nodes);
    let distance = squared_distance(&left_target.center, &right_target.center);
    let radius = &left_target.radius + &right_target.radius;
    assert!(distance > &radius * &radius, "final target balls overlap");
}

#[test]
#[ignore = "requires CUDA; live rechart preserves root balls, covariance and source error"]
fn enclosed_rechart_preserves_root_balls_covariance_and_source_error() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 2;
    let mut base = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed(nodes),
        ResidentGrain(72),
    )
    .unwrap();
    let mut changed = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed(nodes),
        ResidentGrain(72),
    )
    .unwrap();
    let input = vec![phase(1, 0, 7), phase(2, 1, 7)];
    let base_first = base
        .advance(&mut NativeFieldOccurrence::entering(input.clone()))
        .unwrap();
    let changed_first = changed
        .advance(&mut NativeFieldOccurrence::entering(input))
        .unwrap();
    let historic = changed.inspect_source(0).unwrap();
    changed.rechart(&[phase(0, 1, 1), phase(3, 4, 5)]).unwrap();
    let received = vec![phase(2, 3, 7), phase(-1, 4, 7)];
    let base_next = base
        .advance(&mut NativeFieldOccurrence::through(
            base_first.source,
            received.clone(),
        ))
        .unwrap();
    let changed_next = changed
        .advance(&mut NativeFieldOccurrence::through(
            changed_first.source,
            received,
        ))
        .unwrap();
    assert_eq!(
        base.inspect_junction_covariance().unwrap(),
        changed.inspect_junction_covariance().unwrap()
    );
    let left = base_next.junction.as_ref().unwrap().enclosed().unwrap();
    let right = changed_next.junction.as_ref().unwrap().enclosed().unwrap();
    assert_eq!(left, right);
    assert_eq!(changed.inspect_source(0).unwrap(), historic);
}
