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

fn assert_ball_contains(ball: &NativeFieldCurrentBall, exact: &[ExactComplexWaveCurrent]) {
    assert!(
        ball.contains(exact),
        "exact value escaped enclosed current ball"
    );
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

/// Enclosed-junction parity: the device balls contain the exact host rank-one solve
/// `(I + d d*)⁻¹ u = u − d (d*u)/(1 + d*d)` of the same linked reception.
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
