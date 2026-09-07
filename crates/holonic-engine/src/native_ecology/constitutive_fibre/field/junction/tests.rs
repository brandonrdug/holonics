//! CUDA-only regression controls for the paired field junction.
//!
//! The parent module includes this file explicitly.  These tests intentionally keep an exact
//! host reference for a very small chart beside the resident operation; it is an observer and
//! never supplies a native current, source, response, or controller law.

use super::super::super::*;
use crate::dimensional_wave::ExactComplexWaveCurrent;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::ResidentSectionRest;
use num_rational::BigRational as Rat;
use num_traits::Zero;

fn phase(real: i64, imaginary: i64, denominator: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, denominator).unwrap()
}

fn equal_seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    (0..nodes)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}

fn zeros(nodes: usize) -> Vec<NativePhaseCurrent> {
    vec![NativePhaseCurrent::zero(); nodes]
}

fn complex_sum(values: &[ExactComplexWaveCurrent]) -> Rat {
    values
        .iter()
        .map(ExactComplexWaveCurrent::norm_square)
        .sum()
}

fn report_segment(
    rest: &ResidentSectionRest,
    segment: usize,
    dimension: usize,
) -> Vec<ExactComplexWaveCurrent> {
    assert_eq!(rest.rows, 1);
    assert_eq!(rest.width, 4 * (dimension + 1));
    let stride = dimension + 1;
    let at = segment * stride;
    let denominator = rest.intervals[at + dimension].0;
    assert!(denominator > 0);
    (0..dimension / 2)
        .map(|index| {
            assert_eq!(
                rest.intervals[at + 2 * index].0,
                rest.intervals[at + 2 * index].1
            );
            assert_eq!(
                rest.intervals[at + 2 * index + 1].0,
                rest.intervals[at + 2 * index + 1].1
            );
            ExactComplexWaveCurrent::new(
                Rat::new(rest.intervals[at + 2 * index].0.into(), denominator.into()),
                Rat::new(
                    rest.intervals[at + 2 * index + 1].0.into(),
                    denominator.into(),
                ),
            )
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

fn contact_vector(
    step: &NativeFieldStep,
    incoming: &[NativePhaseCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    let mut contact = source_vector(step);
    contact.extend(incoming.iter().map(|value| value.current().negated()));
    contact
}

fn realified_outer(contact: &[ExactComplexWaveCurrent]) -> Vec<Vec<Rat>> {
    let mut result = vec![vec![Rat::zero(); contact.len() * 2]; contact.len() * 2];
    for (left, a) in contact.iter().enumerate() {
        for (right, b) in contact.iter().enumerate() {
            let rr = &a.real * &b.real + &a.imaginary * &b.imaginary;
            let ri = &a.real * &b.imaginary - &a.imaginary * &b.real;
            let ir = &a.imaginary * &b.real - &a.real * &b.imaginary;
            result[2 * left][2 * right] = rr.clone();
            result[2 * left][2 * right + 1] = ri;
            result[2 * left + 1][2 * right] = ir;
            result[2 * left + 1][2 * right + 1] = rr;
        }
    }
    result
}

fn decode_covariance(rest: &ResidentSectionRest, dimension: usize) -> Vec<Vec<Rat>> {
    assert_eq!(rest.rows, 1);
    assert_eq!(rest.width, dimension * dimension + 1);
    let denominator = rest.intervals[dimension * dimension].0;
    assert!(denominator > 0);
    rest.intervals[..dimension * dimension]
        .chunks_exact(dimension)
        .map(|row| {
            row.iter()
                .map(|(lower, upper)| {
                    assert_eq!(lower, upper);
                    Rat::new((*lower).into(), denominator.into())
                })
                .collect()
        })
        .collect()
}

fn assert_matrix_eq(actual: &[Vec<Rat>], expected: &[Vec<Rat>]) {
    assert_eq!(actual.len(), expected.len());
    for (actual_row, expected_row) in actual.iter().zip(expected) {
        assert_eq!(actual_row, expected_row);
    }
}

#[test]
#[ignore = "requires CUDA; exact first paired row and four-segment junction return"]
fn paired_junction_founds_actual_first_row_and_exact_report_shape() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 3;
    let mut body =
        NativeConstitutiveField::found_with_paired_junction(&surface, equal_seed(nodes)).unwrap();
    let incoming = vec![phase(1, 0, 1), phase(0, 1, 1), phase(1, 1, 2)];
    let first = body
        .advance(&mut NativeFieldOccurrence::entering(incoming.clone()))
        .unwrap();
    let reading = first.junction.as_ref().expect("paired reading");
    assert_eq!(reading.potential.len(), 3 * nodes);
    assert_eq!(reading.outgoing.len(), 3 * nodes);
    assert_eq!(reading.held_current.len(), 3 * nodes);
    assert_eq!(reading.potential_prefix.len(), 3 * nodes);

    let covariance = body
        .inspect_junction_covariance()
        .unwrap()
        .expect("covariance");
    let dimension = 6 * nodes;
    let actual = decode_covariance(&covariance, dimension);
    let expected = vec![vec![Rat::zero(); dimension]; dimension];
    assert_matrix_eq(&actual, &expected);
    assert!(body.inspect_junction(0).unwrap().is_some());

    let later = vec![phase(2, 1, 1), phase(-1, 1, 1), phase(1, -2, 1)];
    let contact = contact_vector(&first, &later);
    let step = body
        .advance(&mut NativeFieldOccurrence::through(
            first.source,
            later.clone(),
        ))
        .unwrap();
    let covariance = body
        .inspect_junction_covariance()
        .unwrap()
        .expect("paired covariance after linked reception");
    let actual = decode_covariance(&covariance, dimension);
    assert_matrix_eq(&actual, &realified_outer(&contact));
    assert!(step.junction.is_some());
    assert!(body.inspect_junction(1).unwrap().is_some());
}

#[test]
#[ignore = "requires CUDA; internal junction current decoder and exact energy control"]
fn paired_junction_reconstructs_delayed_contacts_and_conserves_energy() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 2;
    let mut body =
        NativeConstitutiveField::found_with_paired_junction(&surface, equal_seed(nodes)).unwrap();
    let inputs = [
        vec![phase(1, 0, 1), phase(0, 1, 1)],
        vec![phase(2, 1, 1), phase(-1, 1, 1)],
        vec![phase(1, -2, 1), phase(2, 0, 1)],
        vec![phase(2, 3, 1), phase(-1, 4, 1)],
    ];
    let mut handle = None;
    let mut prior_currents: Vec<ExactComplexWaveCurrent> = Vec::new();
    let mut reports = Vec::new();
    for (occurrence, incoming) in inputs.iter().enumerate() {
        let mut event = if occurrence == 1 {
            NativeFieldOccurrence::entering(incoming.clone())
        } else {
            match handle.take() {
                Some(source) => NativeFieldOccurrence::through(source, incoming.clone()),
                None => NativeFieldOccurrence::entering(incoming.clone()),
            }
        };
        let step = body.advance(&mut event).unwrap();
        let report = body.inspect_junction(occurrence).unwrap().expect("report");
        let dimension = 6 * nodes;
        let potential = report_segment(&report, 0, dimension);
        let outgoing = report_segment(&report, 1, dimension);
        let u: Vec<_> = potential
            .iter()
            .zip(&outgoing)
            .map(|(v, b)| v.subtract(b))
            .collect();
        let mut expected_input = source_vector(&step);
        expected_input.extend(vec![ExactComplexWaveCurrent::zero(); nodes]);
        assert_eq!(u, expected_input);
        let next = body
            .inspect_internal_currents()
            .unwrap()
            .expect("internal current report");
        let next_currents: Vec<_> = next.iter().map(|entry| entry.current.clone()).collect();
        assert_eq!(
            complex_sum(&u) + complex_sum(&prior_currents),
            complex_sum(&outgoing) + complex_sum(&next_currents)
        );
        if occurrence > 0 {
            // The current update is checked from the actual potential independently of the
            // prefix decoder: b_i' = d_i^* v_t - b_i.
            let current_report = body.inspect_junction(occurrence).unwrap().unwrap();
            let current_potential = report_segment(&current_report, 0, dimension);
            for entry in &next {
                let prior = reports
                    .last()
                    .and_then(|entries: &Vec<NativeFieldInternalCurrent>| {
                        entries
                            .iter()
                            .find(|old| old.receiving_occurrence == entry.receiving_occurrence)
                    })
                    .map(|old| old.current.clone())
                    .unwrap_or_else(ExactComplexWaveCurrent::zero);
                let updated = entry
                    .contact
                    .iter()
                    .zip(&current_potential)
                    .fold(ExactComplexWaveCurrent::zero(), |sum, (d, v)| {
                        sum.add(&d.conjugate().multiply(v))
                    })
                    .subtract(&prior);
                assert_eq!(entry.current, updated);
            }
        }
        reports.push(next);
        prior_currents = next_currents;
        if occurrence == 1 {
            drop(step.source);
        } else {
            handle = Some(step.source);
        }
    }

    // The executable decoder uses the final current prefix P_t, each contact's retained birth
    // prefix P_j, and one sign determined by the final current time t.
    let final_occurrence = body.occurrence_count() - 1;
    let final_report = body.inspect_junction(final_occurrence).unwrap().unwrap();
    let final_prefix = report_segment(&final_report, 3, 6 * nodes);
    let final_sign = if body.occurrence_count() % 2 == 1 {
        Rat::from_integer(1.into())
    } else {
        Rat::from_integer((-1).into())
    };
    for entry in body.inspect_internal_currents().unwrap().unwrap() {
        let birth = report_segment(
            &body
                .inspect_junction(entry.receiving_occurrence - 1)
                .unwrap()
                .unwrap(),
            3,
            6 * nodes,
        );
        let decoded = entry
            .contact
            .iter()
            .zip(final_prefix.iter().zip(&birth))
            .fold(ExactComplexWaveCurrent::zero(), |sum, (d, (p, p_birth))| {
                sum.add(&d.conjugate().multiply(&p.subtract(p_birth)))
            })
            .scaled(&final_sign);
        assert_eq!(entry.current, decoded);
    }
}

#[test]
#[ignore = "requires CUDA; equal paired covariance with divergent retained native history"]
fn paired_junction_same_future_input_retains_history_difference_under_equal_covariance() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut left =
        NativeConstitutiveField::found_with_paired_junction(&surface, equal_seed(1)).unwrap();
    let mut right =
        NativeConstitutiveField::found_with_paired_junction(&surface, equal_seed(1)).unwrap();
    for body in [&mut left, &mut right] {
        let first = body
            .advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 1)]))
            .unwrap();
        body.advance(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(0, 1, 1)],
        ))
        .unwrap();
    }
    let moment = left.inspect_junction_covariance().unwrap();
    assert_eq!(moment, right.inspect_junction_covariance().unwrap());
    left.advance(&mut NativeFieldOccurrence::entering(vec![phase(1, 0, 1)]))
        .unwrap();
    right
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(-1, 0, 1)]))
        .unwrap();
    // Two common arrivals align BOTH raw branches of the matched primary junction, while the
    // learned junction's internal current retains the earlier differing physical input.
    for _ in 0..2 {
        left.advance(&mut NativeFieldOccurrence::entering(zeros(1)))
            .unwrap();
        right
            .advance(&mut NativeFieldOccurrence::entering(zeros(1)))
            .unwrap();
    }
    let left_step = left
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(0, 1, 1)]))
        .unwrap();
    let right_step = right
        .advance(&mut NativeFieldOccurrence::entering(vec![phase(0, 1, 1)]))
        .unwrap();
    assert_eq!(source_vector(&left_step), source_vector(&right_step));
    assert_eq!(left_step.lineage.incoming, right_step.lineage.incoming);
    assert_eq!(
        left.inspect_relation().unwrap(),
        right.inspect_relation().unwrap()
    );
    assert_eq!(left.inspect_junction_covariance().unwrap(), moment);
    assert_eq!(right.inspect_junction_covariance().unwrap(), moment);
    let a = left_step.junction.unwrap();
    let b = right_step.junction.unwrap();
    assert_ne!(a.held_current, b.held_current);
    assert_ne!(a.outgoing[2..], b.outgoing[2..]);
}

#[test]
#[ignore = "requires CUDA; rechart preserves root junction response and historic source frame"]
fn paired_junction_rechart_preserves_root_response_and_historic_source() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 2;
    let mut base =
        NativeConstitutiveField::found_with_paired_junction(&surface, equal_seed(nodes)).unwrap();
    let mut changed =
        NativeConstitutiveField::found_with_paired_junction(&surface, equal_seed(nodes)).unwrap();
    let input = vec![phase(1, 0, 1), phase(0, 1, 1)];
    let base_first = base
        .advance(&mut NativeFieldOccurrence::entering(input.clone()))
        .unwrap();
    let changed_first = changed
        .advance(&mut NativeFieldOccurrence::entering(input))
        .unwrap();
    let historic = changed.inspect_source(0).unwrap();
    changed.rechart(&[phase(0, 1, 1), phase(3, 4, 5)]).unwrap();
    let received = vec![phase(2, 3, 1), phase(-1, 4, 1)];
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
    let base_reading = base_next.junction.unwrap();
    let changed_reading = changed_next.junction.unwrap();
    assert_eq!(base_reading, changed_reading);
    assert_eq!(
        base.inspect_internal_currents().unwrap(),
        changed.inspect_internal_currents().unwrap()
    );
    assert_eq!(changed.inspect_source(0).unwrap(), historic);
}

#[test]
#[ignore = "requires CUDA; wide paired covariance refuses before body commit and retains handle"]
fn paired_junction_arithmetic_refusal_preserves_old_body_and_recoverable_handle() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut seed = equal_seed(1);
    seed[0].initial_held = phase(1, 0, 1);
    let mut body = NativeConstitutiveField::found_with_paired_junction(&surface, seed).unwrap();
    let first = body
        .advance(&mut NativeFieldOccurrence::entering(zeros(1)))
        .unwrap();
    let before_relation = body.inspect_relation().unwrap();
    let before_held = body.inspect_held().unwrap();
    let before_source = body.inspect_source(0).unwrap();
    let before_covariance = body.inspect_junction_covariance().unwrap();
    let denominator = 3_037_000_501_i64;
    // The unconnected field's original source/relation carrier admits this same occurrence.
    // Its refusal in the connected body is the moment's wider required arithmetic.
    let mut control_seed = equal_seed(1);
    control_seed[0].initial_held = phase(1, 0, 1);
    let mut control = NativeConstitutiveField::found(&surface, control_seed).unwrap();
    let control_source = control
        .advance(&mut NativeFieldOccurrence::entering(zeros(1)))
        .unwrap();
    control
        .advance(&mut NativeFieldOccurrence::through(
            control_source.source,
            vec![phase(1, 0, denominator)],
        ))
        .unwrap();
    let mut refused = NativeFieldOccurrence::through(first.source, vec![phase(1, 0, denominator)]);
    let refused_result = body.advance(&mut refused);
    assert!(matches!(
        refused_result,
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.occurrence_count(), 1);
    assert_eq!(body.inspect_relation().unwrap(), before_relation);
    assert_eq!(body.inspect_held().unwrap(), before_held);
    assert_eq!(body.inspect_source(0).unwrap(), before_source);
    assert_eq!(
        body.inspect_junction_covariance().unwrap(),
        before_covariance
    );
    let handle = refused
        .take_source()
        .expect("refusal retains old source handle");
    body.advance(&mut NativeFieldOccurrence::through(handle, zeros(1)))
        .unwrap();
    assert_eq!(body.occurrence_count(), 2);
}
