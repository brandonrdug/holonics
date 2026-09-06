use super::super::super::tests::row_space;
use super::super::tests::{exterior, material, phase};
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn relation_rows(body: &NativeConstitutiveEcology<'_>) -> Vec<Vec<Rat>> {
    let rest = body.inspect_relation().unwrap();
    rest.intervals
        .chunks_exact(rest.width)
        .map(|r| {
            r.iter()
                .map(|(a, b)| {
                    assert_eq!(a, b);
                    Rat::from_integer((*a).into())
                })
                .collect()
        })
        .collect()
}
fn check_difference(
    base: &NativeReceivedCurrentDifference,
    changed: &NativeReceivedCurrentDifference,
    frame: &NativeCurrentFrame,
    source: &[ExactComplexWaveCurrent],
    before: Vec<Vec<Rat>>,
) {
    assert_eq!(base.source_occurrence, changed.source_occurrence);
    assert_eq!(base.arrived, changed.arrived);
    let source = source
        .iter()
        .flat_map(|v| [v.real.clone(), v.imaginary.clone()])
        .collect::<Vec<_>>();
    let source_width = source.len();
    let domain = before
        .iter()
        .map(|r| r[..source_width].to_vec())
        .collect::<Vec<_>>();
    let in_span = |rows: &[Vec<Rat>], vector: Vec<Rat>| {
        let mut extended = rows.to_vec();
        extended.push(vector);
        row_space(extended) == row_space(rows.to_vec())
    };
    match (&base.former_receiver_fibre, &changed.former_receiver_fibre) {
        (
            ConstitutiveReading::OutsideDomain {
                source_remainder: a,
            },
            ConstitutiveReading::OutsideDomain {
                source_remainder: b,
            },
        ) => {
            let root = b
                .chunks_exact(2)
                .zip(frame.root_to_local())
                .flat_map(|(pair, g)| {
                    let v = g
                        .current()
                        .conjugate()
                        .multiply(&ExactComplexWaveCurrent::new(
                            pair[0].clone(),
                            pair[1].clone(),
                        ));
                    [v.real, v.imaginary]
                })
                .collect::<Vec<_>>();
            assert!(in_span(
                &domain,
                source.iter().zip(a).map(|(s, r)| s - r).collect()
            ));
            assert!(in_span(
                &domain,
                source.iter().zip(&root).map(|(s, r)| s - r).collect()
            ));
            assert!(in_span(
                &domain,
                root.iter().zip(a).map(|(b, a)| b - a).collect()
            ));
            assert!(
                !in_span(&domain, a.clone()),
                "the source obstruction must be genuinely outside its domain"
            );
        }
        (
            ConstitutiveReading::Unique { current: a },
            ConstitutiveReading::Unique { current: b },
        ) => {
            assert_eq!(a, b);
            let mut pair = source;
            pair.extend(a.clone());
            assert!(in_span(&before, pair));
        }
        (
            ConstitutiveReading::Plural {
                particular: a,
                directions: ad,
            },
            ConstitutiveReading::Plural {
                particular: b,
                directions: bd,
            },
        ) => {
            assert_eq!(row_space(ad.clone()), row_space(bd.clone()));
            assert!(in_span(ad, b.iter().zip(a).map(|(b, a)| b - a).collect()));
            let mut pair = source;
            pair.extend(a.clone());
            assert!(in_span(&before, pair));
        }
        _ => panic!("the complete receiver fibre changed species under rechart"),
    }
}

fn check_state(base: &NativeConstitutiveEcology<'_>, changed: &NativeConstitutiveEcology<'_>) {
    let a = base.inspect_held().unwrap();
    let b = changed.inspect_held().unwrap();
    let frame = changed
        .relation
        .surface
        .read_out(&changed.frame.native)
        .unwrap();
    for (node, g) in changed.current_frame().root_to_local().iter().enumerate() {
        assert_eq!(frame[3 * node..3 * node + 3], g.words().map(|v| (v, v)));
        let old = &base.material()[node];
        let new = &changed.material()[node];
        assert_eq!(old.incoming_admittance, new.incoming_admittance);
        assert_eq!(old.held_admittance, new.held_admittance);
        assert_eq!(
            new.incoming_transport.current(),
            g.current().multiply(&old.incoming_transport.current())
        );
        assert_eq!(
            new.initial_held.current(),
            g.current().multiply(&old.initial_held.current())
        );
        let before = phase(
            a.intervals[3 * node].0,
            a.intervals[3 * node + 1].0,
            a.intervals[3 * node + 2].0,
        )
        .current();
        let after = phase(
            b.intervals[3 * node].0,
            b.intervals[3 * node + 1].0,
            b.intervals[3 * node + 2].0,
        )
        .current();
        assert_eq!(after, g.current().multiply(&before));
    }
    let transformed = relation_rows(base)
        .into_iter()
        .map(|mut row| {
            for (node, g) in changed.current_frame().root_to_local().iter().enumerate() {
                let v = g.current().multiply(&ExactComplexWaveCurrent::new(
                    row[2 * node].clone(),
                    row[2 * node + 1].clone(),
                ));
                row[2 * node] = v.real;
                row[2 * node + 1] = v.imaginary;
            }
            row
        })
        .collect();
    assert_eq!(row_space(relation_rows(changed)), row_space(transformed));
}

#[test]
#[ignore = "requires CUDA; entire live rechart with delayed original-frame source handles"]
fn live_rechart_preserves_state_relation_and_old_receiving_sources() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut base = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut changed = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut a = base
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let mut b = changed
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    for _ in 0..3 {
        let input = exterior(&a.root_source_currents());
        a = base
            .advance(&mut NativeCurrentOccurrence::through(a.source, input))
            .unwrap();
        b = changed
            .advance(&mut NativeCurrentOccurrence::through(b.source, input))
            .unwrap();
    }
    let later_a = base
        .advance(&mut NativeCurrentOccurrence::entering(phase(0, 1, 1)))
        .unwrap();
    let later_b = changed
        .advance(&mut NativeCurrentOccurrence::entering(phase(0, 1, 1)))
        .unwrap();
    let original = surface.read_out(&changed.history[3].section).unwrap();
    let old_incidence = changed.incidence(3).unwrap();
    let before = changed.census();
    changed.rechart(&[phase(3, 4, 5), phase(0, -1, 1)]).unwrap();
    assert_eq!(
        changed.current_frame().root_to_local(),
        &[phase(3, 4, 5), phase(0, -1, 1)]
    );
    let after = changed.census();
    assert_eq!(after.deed_launches - before.deed_launches, 1);
    assert_eq!(after.ingress_octets - before.ingress_octets, 12 * 16);
    assert_eq!(
        after.egress_section_octets - before.egress_section_octets,
        18 * 16
    );
    assert_eq!(after.section_read_outs - before.section_read_outs, 1);
    assert_eq!(
        surface.read_out(&changed.history[3].section).unwrap(),
        original
    );
    assert_eq!(changed.incidence(3).unwrap(), old_incidence);
    check_state(&base, &changed);
    let source = a.root_source_currents();
    let before = relation_rows(&base);
    let incoming = exterior(&source);
    let a = base
        .advance(&mut NativeCurrentOccurrence::through(a.source, incoming))
        .unwrap();
    let b = changed
        .advance(&mut NativeCurrentOccurrence::through(b.source, incoming))
        .unwrap();
    assert_eq!(b.lineage.received_from, Some(3));
    assert_eq!(b.lineage.predecessor_state, Some(4));
    assert_eq!(a.root_source_currents(), b.root_source_currents());
    assert_eq!(a.receiver, b.receiver);
    check_difference(
        a.received_difference.as_ref().unwrap(),
        b.received_difference.as_ref().unwrap(),
        &b.frame,
        &source,
        before,
    );
    check_state(&base, &changed);
    let crossing = changed.joined_incidence(4, 5).unwrap();
    assert_eq!(crossing.len(), 8);
    assert!(crossing.iter().any(|c| c.first.target != c.second.source));
    for c in crossing {
        assert_eq!(
            c.middle_transport,
            changed.current_frame().root_to_local[c.first.node].current()
        );
    }

    let old_frame = Rc::clone(&changed.frame.view);
    let gauges = [phase(0, 1, 1), phase(4, 3, 5)];
    changed.rechart(&gauges).unwrap();
    for ((actual, gauge), old) in changed
        .current_frame()
        .root_to_local()
        .iter()
        .zip(gauges)
        .zip(old_frame.root_to_local())
    {
        assert_eq!(actual.current(), gauge.current().multiply(&old.current()));
    }
    let source = later_a.root_source_currents();
    let before = relation_rows(&base);
    let incoming = exterior(&source);
    let a = base
        .advance(&mut NativeCurrentOccurrence::through(
            later_a.source,
            incoming,
        ))
        .unwrap();
    let b = changed
        .advance(&mut NativeCurrentOccurrence::through(
            later_b.source,
            incoming,
        ))
        .unwrap();
    assert_eq!(a.root_source_currents(), b.root_source_currents());
    assert_eq!(a.receiver, b.receiver);
    check_difference(
        a.received_difference.as_ref().unwrap(),
        b.received_difference.as_ref().unwrap(),
        &b.frame,
        &source,
        before,
    );
    check_state(&base, &changed);
    assert_eq!(changed.history[4].frame.view.ordinal, 0);
    assert_eq!(changed.recharts().len(), 2);
}

#[test]
#[ignore = "requires CUDA; inverse rechart and zero development retain distinct occurrences"]
fn inverse_gauge_recovers_the_live_relation_without_erasing_frame_history() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let first = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let before = body.inspect_held().unwrap();
    let relation = body.inspect_relation().unwrap();
    let seed = body.material().to_vec();
    body.rechart(&[phase(3, 4, 5), phase(0, 1, 1)]).unwrap();
    body.rechart(&[phase(3, -4, 5), phase(0, -1, 1)]).unwrap();
    assert_eq!(body.inspect_held().unwrap(), before);
    assert_eq!(body.inspect_relation().unwrap(), relation);
    assert_eq!(body.material(), seed.as_slice());
    assert_eq!(body.current_frame().ordinal(), 2);
    assert_eq!(body.lineage().count(), 1);
    let received = body
        .advance(&mut NativeCurrentOccurrence::through(
            first.source,
            phase(1, 0, 1),
        ))
        .unwrap();
    assert_eq!(received.lineage.received_from, Some(0));
    let mut zero = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let first = zero
        .advance(&mut NativeCurrentOccurrence::entering(
            NativePhaseCurrent::zero(),
        ))
        .unwrap();
    zero.rechart(&[NativePhaseCurrent::unit(); 2]).unwrap();
    let next = zero
        .advance(&mut NativeCurrentOccurrence::through(
            first.source,
            NativePhaseCurrent::zero(),
        ))
        .unwrap();
    assert_eq!(next.formed_pivot, None);
    assert_eq!(next.successor_rank, 0);
    assert_eq!(zero.lineage().count(), 2);
}

#[test]
#[ignore = "requires CUDA; physical incidence change is not a re-expression"]
fn physical_change_preserves_historical_material_but_changes_the_new_current() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut base = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut gauge = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut physical = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    for body in [&mut base, &mut gauge, &mut physical] {
        body.advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
            .unwrap();
    }
    let old = physical.incidence(0).unwrap();
    let held = physical.inspect_held().unwrap();
    let r = physical.inspect_relation().unwrap();
    gauge
        .rechart(&[phase(0, 1, 1), NativePhaseCurrent::unit()])
        .unwrap();
    physical
        .replace_incoming_transport(0, phase(0, 1, 1))
        .unwrap();
    assert_eq!(physical.inspect_held().unwrap(), held);
    assert_eq!(physical.inspect_relation().unwrap(), r);
    assert_eq!(physical.incidence(0).unwrap(), old);
    assert_eq!(
        physical.material_at(0).unwrap()[0].incoming_transport,
        NativePhaseCurrent::unit()
    );
    let a = base
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 1, 1)))
        .unwrap();
    let b = gauge
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 1, 1)))
        .unwrap();
    let c = physical
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 1, 1)))
        .unwrap();
    assert_eq!(a.root_source_currents(), b.root_source_currents());
    assert_ne!(a.root_source_currents()[0], c.root_source_currents()[0]);
    assert_eq!(a.root_source_currents()[1], c.root_source_currents()[1]);
    assert_eq!(physical.current_frame().ordinal(), 0);
    assert_eq!(physical.incidence_changes().len(), 1);
}

#[test]
#[ignore = "requires CUDA; failed gauge never partially changes the live body"]
fn refused_rechart_preserves_the_body_and_its_pending_source_handles() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut seed = material();
    seed[0].initial_held = phase(23, 17, 7);
    let mut body = NativeConstitutiveEcology::found(&surface, seed).unwrap();
    let first = body
        .advance(&mut NativeCurrentOccurrence::entering(
            NativePhaseCurrent::zero(),
        ))
        .unwrap();
    let held = body.inspect_held().unwrap();
    let relation = body.inspect_relation().unwrap();
    let material = body.material().to_vec();
    let before = body.census();
    assert!(matches!(
        body.rechart(&[phase(1, 1, 1), NativePhaseCurrent::unit()]),
        Err(ConstitutiveFibreError::Shape)
    ));
    assert_eq!(body.census(), before);
    let huge = phase(
        999_999_999_999_999_999,
        2_000_000_000,
        1_000_000_000_000_000_001,
    );
    assert!(matches!(
        body.rechart(&[huge, NativePhaseCurrent::unit()]),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.inspect_held().unwrap(), held);
    assert_eq!(body.inspect_relation().unwrap(), relation);
    assert_eq!(body.material(), material.as_slice());
    assert_eq!(body.current_frame().ordinal(), 0);
    assert!(body.recharts().is_empty());
    body.advance(&mut NativeCurrentOccurrence::through(
        first.source,
        phase(1, 0, 1),
    ))
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; equal outward readings do not determine the developing successor"]
fn equal_emission_keeps_different_held_consequences() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    };
    let mut a = NativeConstitutiveEcology::found(&surface, vec![seed.clone()]).unwrap();
    let mut b = NativeConstitutiveEcology::found(&surface, vec![seed]).unwrap();
    let left = a
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let right = b
        .advance(&mut NativeCurrentOccurrence::entering(phase(2, 0, 1)))
        .unwrap();
    assert_eq!(left.source_currents, right.source_currents);
    assert_eq!(left.receiver, right.receiver);
    assert_ne!(a.inspect_held().unwrap(), b.inspect_held().unwrap());
    assert_ne!(left.lineage.incoming, right.lineage.incoming);
}

#[test]
#[ignore = "requires CUDA; a live rechart preserves a genuinely plural receiver fibre"]
fn plural_receiver_and_its_later_comparison_survive_rechart() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: phase(1, 0, 1),
    };
    let mut base = NativeConstitutiveEcology::found(&surface, vec![seed.clone()]).unwrap();
    let mut changed = NativeConstitutiveEcology::found(&surface, vec![seed]).unwrap();
    fn expose(body: &mut NativeConstitutiveEcology<'_>) -> NativeCurrentStep {
        let first = body
            .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
            .unwrap();
        let second = body
            .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
            .unwrap();
        body.advance(&mut NativeCurrentOccurrence::through(
            first.source,
            phase(3, 0, 1),
        ))
        .unwrap();
        body.advance(&mut NativeCurrentOccurrence::through(
            second.source,
            phase(4, 0, 1),
        ))
        .unwrap()
    }
    let a = expose(&mut base);
    let b = expose(&mut changed);
    let before = relation_rows(&base);
    let source = a.root_source_currents();
    changed.rechart(&[phase(3, 4, 5)]).unwrap();
    check_state(&base, &changed);
    let a = base
        .advance(&mut NativeCurrentOccurrence::through(
            a.source,
            phase(5, 0, 1),
        ))
        .unwrap();
    let b = changed
        .advance(&mut NativeCurrentOccurrence::through(
            b.source,
            phase(5, 0, 1),
        ))
        .unwrap();
    assert_eq!(a.root_source_currents(), b.root_source_currents());
    assert_ne!(a.source_currents, b.source_currents);
    check_difference(
        a.received_difference.as_ref().unwrap(),
        b.received_difference.as_ref().unwrap(),
        &b.frame,
        &source,
        before,
    );
    match (&a.receiver, &b.receiver) {
        (
            ConstitutiveReading::Plural {
                particular: a,
                directions: ad,
            },
            ConstitutiveReading::Plural {
                particular: b,
                directions: bd,
            },
        ) => {
            assert_eq!(row_space(ad.clone()), row_space(bd.clone()));
            let mut extended = ad.clone();
            extended.push(b.iter().zip(a).map(|(b, a)| b - a).collect());
            assert_eq!(row_space(extended), row_space(ad.clone()));
        }
        _ => panic!("rechart selected an answer from a plural fibre"),
    }
    check_state(&base, &changed);
}
