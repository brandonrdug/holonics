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

/// Paired-junction power balance: `|u|² + |b|² = |outgoing|² + |b′|²` for every occurrence,
/// and the device internal-current update equals the exact host `b′ = d*·v − b`.
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
