use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn phase(a: i64, b: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(a, b, d).unwrap()
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
fn zero(nodes: usize) -> Vec<NativePhaseCurrent> {
    vec![NativePhaseCurrent::zero(); nodes]
}
fn decoded(values: &ResidentSectionRest) -> Vec<ExactComplexWaveCurrent> {
    values
        .intervals
        .chunks_exact(3)
        .map(|v| phase(v[0].0, v[1].0, v[2].0).current())
        .collect()
}
fn paired_vector(field: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    field
        .iter()
        .flat_map(|v| [v.real.clone(), v.imaginary.clone()])
        .collect()
}

#[test]
#[cfg(target_os = "macos")]
#[ignore = "requires Metal; unported material transport refuses before native state changes"]
fn metal_unported_material_transport_refuses_without_changing_the_field() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface, equal_seed(1), ResidentGrain(72),
    ).unwrap();
    field.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent).unwrap();
    let before = (field.inspect_relation().unwrap(), field.inspect_held().unwrap());
    let launches = field.census().deed_launches;
    let mut occurrence = NativeFieldOccurrence::entering(vec![phase(1, 1, 1)]);
    let error = field.advance_resident(&mut occurrence).err().expect("unported material transport");
    assert!(error.to_string().contains("contextual material transport is not yet implemented on Metal"));
    assert_eq!(field.occurrence_count(), 0);
    assert!(field.pending_lineage().is_none());
    assert_eq!(field.census().deed_launches, launches);
    assert_eq!(
        (field.inspect_relation().unwrap(), field.inspect_held().unwrap()),
        before,
    );
}

#[test]
#[cfg(target_os = "macos")]
#[ignore = "requires Metal; complete field scratch aperture and full-width rechart"]
fn metal_field_aperture_covers_the_last_rechart_coordinate() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let available = surface.declaration().max_sectiond_bytes as usize;
    let nodes = (1..=available)
        .take_while(|n| ResidentSurface::constitutive_field_scratch(*n).unwrap() <= available)
        .last()
        .unwrap();
    assert!(matches!(
        NativeConstitutiveField::found(&surface, equal_seed(nodes + 1)),
        Err(ConstitutiveFibreError::ScratchAperture { .. })
    ));
    let mut field = NativeConstitutiveField::found(&surface, equal_seed(nodes)).unwrap();
    let first = field
        .advance_status(&mut NativeFieldOccurrence::entering(
            vec![NativePhaseCurrent::unit(); nodes],
        ))
        .unwrap();
    field
        .advance_status(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(2, 1, 1); nodes],
        ))
        .unwrap();
    let historical = field.inspect_source(0).unwrap();
    field.rechart(&vec![phase(0, 1, 1); nodes]).unwrap();
    assert_eq!(field.inspect_source(0).unwrap(), historical);
    let relation = field.inspect_relation().unwrap();
    assert!(
        relation
            .intervals
            .chunks_exact(relation.width)
            .any(|row| row.last().unwrap().0 != 0)
    );
    assert_eq!(field.current_frame().ordinal(), 1);
    assert_eq!(field.occurrence_count(), 2);
}

#[test]
#[ignore = "requires native field; borrowed profile adds no device readout and consumes no handle"]
fn field_profile_borrows_history_without_changing_native_ownership() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let first = field
        .advance_status(&mut NativeFieldOccurrence::entering(vec![
            phase(1, 0, 1),
            phase(0, 1, 1),
        ]))
        .unwrap();
    let before = field.census();
    {
        let profile = field.intrinsic_profile();
        assert_eq!(profile.extents.source_extent, 8);
        assert_eq!(profile.extents.target_extent, 4);
        assert_eq!(profile.lineages[0], field.lineage(0).unwrap());
        assert!(std::ptr::eq(
            profile.source_frames[0],
            field.source_frame(0).unwrap()
        ));
        assert!(std::ptr::eq(profile.material, field.material()));
        assert_eq!(profile.reconstruction_extent, 1);
    }
    assert_eq!(field.census(), before);
    let next = field
        .advance_status(&mut NativeFieldOccurrence::through(first.source, zero(2)))
        .unwrap();
    assert_eq!(next.lineage.received_from, Some(0));
}

#[test]
#[ignore = "requires CUDA; complete independent port currents and actual held successor"]
fn field_scattering_returns_both_branches_with_weighted_energy() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let seeds = vec![
        NativeJunctionSeed {
            incoming_admittance: 2,
            held_admittance: 5,
            incoming_transport: phase(3, 4, 5),
            initial_held: phase(1, 2, 3),
        },
        NativeJunctionSeed {
            incoming_admittance: 3,
            held_admittance: 1,
            incoming_transport: phase(0, 1, 1),
            initial_held: phase(-2, 1, 4),
        },
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 2,
            incoming_transport: phase(-1, 0, 1),
            initial_held: phase(2, -1, 3),
        },
    ];
    let mut body = NativeConstitutiveField::found(&surface, seeds.clone()).unwrap();
    let incoming = vec![phase(2, -1, 7), phase(3, 2, 5), phase(-1, 4, 3)];
    let step = body
        .advance(&mut NativeFieldOccurrence::entering(incoming.clone()))
        .unwrap();
    for (i, seed) in seeds.iter().enumerate() {
        let a = seed
            .incoming_transport
            .current()
            .multiply(&incoming[i].current());
        let h = seed.initial_held.current();
        let ya = Rat::from_integer(seed.incoming_admittance.into());
        let yh = Rat::from_integer(seed.held_admittance.into());
        let v = a
            .scaled(&ya)
            .add(&h.scaled(&yh))
            .scaled(&(Rat::from_integer(2.into()) / (&ya + &yh)));
        assert_eq!(step.outgoing[i], v.subtract(&a));
        assert_eq!(step.held_successor[i], v.subtract(&h));
        assert_eq!(
            &ya * a.norm_square() + &yh * h.norm_square(),
            &ya * step.outgoing[i].norm_square() + &yh * step.held_successor[i].norm_square()
        );
    }
    assert_eq!(decoded(&body.inspect_held().unwrap()), step.held_successor);
    let source = body.inspect_source(0).unwrap();
    let den = source.intervals[12].0;
    for i in 0..3 {
        assert_eq!(
            phase(
                source.intervals[4 * i].0,
                source.intervals[4 * i + 1].0,
                den
            )
            .current(),
            step.outgoing[i]
        );
        assert_eq!(
            phase(
                source.intervals[4 * i + 2].0,
                source.intervals[4 * i + 3].0,
                den
            )
            .current(),
            step.held_successor[i]
        );
    }
    let again = body
        .advance(&mut NativeFieldOccurrence::entering(incoming))
        .unwrap();
    assert_ne!(again.outgoing, step.outgoing);
    assert_eq!(again.lineage.predecessor_state, Some(0));
    assert_eq!(body.inspect_source(0).unwrap(), source);
}

#[test]
#[ignore = "requires CUDA; same outward receiver can retain different held/source branches"]
fn equal_outward_faces_do_not_erase_the_complete_source_field() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut a = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut b = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let x = a
        .advance(&mut NativeFieldOccurrence::entering(vec![
            phase(1, 0, 1),
            phase(0, 1, 1),
        ]))
        .unwrap();
    let y = b
        .advance(&mut NativeFieldOccurrence::entering(vec![
            phase(0, 1, 1),
            phase(1, 0, 1),
        ]))
        .unwrap();
    assert_eq!(x.outgoing, y.outgoing);
    assert_ne!(x.held_successor, y.held_successor);
    assert_ne!(a.inspect_source(0).unwrap(), b.inspect_source(0).unwrap());
    assert_eq!(x.lineage.incoming.len(), 2);
}

#[test]
#[ignore = "requires CUDA; actual linked full-field relation changes a new current's receiver"]
fn paired_source_changes_later_full_field_conduct_and_unlinked_control_stays_open() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut learned = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut control = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let first = vec![phase(1, 0, 1), phase(0, 1, 1)];
    let actual_return = vec![phase(2, 3, 1), phase(-1, 4, 1)];
    let source = learned
        .advance(&mut NativeFieldOccurrence::entering(first.clone()))
        .unwrap();
    control
        .advance(&mut NativeFieldOccurrence::entering(first))
        .unwrap();
    let received = learned
        .advance(&mut NativeFieldOccurrence::through(
            source.source,
            actual_return.clone(),
        ))
        .unwrap();
    control
        .advance(&mut NativeFieldOccurrence::entering(actual_return.clone()))
        .unwrap();
    assert_eq!(received.lineage.received_from, Some(0));
    assert_eq!(
        received.received_difference.unwrap().arrived,
        actual_return
            .iter()
            .map(|p| p.current())
            .collect::<Vec<_>>()
    );
    assert_eq!(received.successor_rank, 1);
    learned
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    control
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let fresh = vec![phase(2, 0, 1), phase(0, 2, 1)];
    let later = learned
        .advance(&mut NativeFieldOccurrence::entering(fresh.clone()))
        .unwrap();
    let matched = control
        .advance(&mut NativeFieldOccurrence::entering(fresh))
        .unwrap();
    assert_eq!(later.outgoing, matched.outgoing);
    assert_eq!(later.held_successor, matched.held_successor);
    assert_eq!(
        later.receiver,
        ConstitutiveReading::Unique {
            current: paired_vector(
                &actual_return
                    .iter()
                    .map(|p| p.current().scaled(&Rat::from_integer(2.into())))
                    .collect::<Vec<_>>()
            )
        }
    );
    assert!(matches!(
        matched.receiver,
        ConstitutiveReading::OutsideDomain { .. }
    ));
}

#[test]
#[ignore = "requires CUDA; zero-source full-field discrepancy retains its vertical fibre"]
fn zero_source_discrepancy_remains_a_full_plural_receiver() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let source = body
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    body.advance(&mut NativeFieldOccurrence::through(
        source.source,
        vec![phase(2, 0, 1), phase(0, 4, 1)],
    ))
    .unwrap();
    body.advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let result = body
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    match result.receiver {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => {
            assert!(particular.iter().all(Rat::is_zero));
            assert_eq!(
                directions,
                vec![
                    vec![1, 0, 0, 2]
                        .into_iter()
                        .map(|v| Rat::from_integer(v.into()))
                        .collect::<Vec<_>>()
                ]
            );
        }
        other => panic!("lost full vertical fibre: {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; source and shape refusals preserve actual handles and body"]
fn foreign_source_and_shape_do_not_consume_a_receiving_handle() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut a = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut b = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let source = a
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let mut occurrence = NativeFieldOccurrence::through(source.source, zero(2));
    assert!(matches!(
        b.advance(&mut occurrence),
        Err(ConstitutiveFibreError::ForeignOccurrence)
    ));
    assert_eq!(b.occurrence_count(), 0);
    let source = occurrence.take_source().expect("unconsumed actual source");
    let mut bad = NativeFieldOccurrence::through(source, zero(1));
    assert!(matches!(
        a.advance(&mut bad),
        Err(ConstitutiveFibreError::Shape)
    ));
    assert_eq!(a.occurrence_count(), 1);
    let source = bad.take_source().unwrap();
    a.advance(&mut NativeFieldOccurrence::through(source, zero(2)))
        .unwrap();
    assert_eq!(a.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; arithmetic refusal publishes no partial memory or relation row"]
fn field_arithmetic_refusal_preserves_source_relation_and_phase() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut seed = equal_seed(1);
    seed[0].incoming_admittance = i64::MAX;
    seed[0].held_admittance = 2;
    let mut body = NativeConstitutiveField::found(&surface, seed).unwrap();
    let source = body
        .advance(&mut NativeFieldOccurrence::entering(zero(1)))
        .unwrap();
    let before = (
        body.inspect_relation().unwrap(),
        body.inspect_held().unwrap(),
        body.inspect_source(0).unwrap(),
    );
    let mut incoming = NativeFieldOccurrence::through(source.source, vec![phase(1, 0, 1)]);
    assert!(matches!(
        body.advance(&mut incoming),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.occurrence_count(), 1);
    assert!(body.pending_lineage().is_none());
    assert_eq!(
        (
            body.inspect_relation().unwrap(),
            body.inspect_held().unwrap(),
            body.inspect_source(0).unwrap()
        ),
        before
    );
    let handle = incoming.take_source().expect("refusal retains source");
    body.advance(&mut NativeFieldOccurrence::through(handle, zero(1)))
        .unwrap();
    assert_eq!(body.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; local source gauges carry both branches and preserve root receiver"]
fn joint_phase_chart_changes_do_not_change_the_qualified_root_response() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let turns = [phase(0, 1, 1), phase(3, 4, 5)];
    let mut gauged = equal_seed(2);
    for (seed, turn) in gauged.iter_mut().zip(turns) {
        seed.incoming_transport = turn;
    }
    let mut a = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut b = NativeConstitutiveField::found(&surface, gauged).unwrap();
    let inputs = vec![phase(1, 0, 1), phase(0, 1, 1)];
    let first_a = a
        .advance(&mut NativeFieldOccurrence::entering(inputs.clone()))
        .unwrap();
    let first_b = b
        .advance(&mut NativeFieldOccurrence::entering(inputs))
        .unwrap();
    for i in 0..2 {
        assert_eq!(
            turns[i].current().multiply(&first_a.outgoing[i]),
            first_b.outgoing[i]
        );
        assert_eq!(
            turns[i].current().multiply(&first_a.held_successor[i]),
            first_b.held_successor[i]
        );
    }
    let received = vec![phase(2, 3, 1), phase(-1, 4, 1)];
    a.advance(&mut NativeFieldOccurrence::through(
        first_a.source,
        received.clone(),
    ))
    .unwrap();
    b.advance(&mut NativeFieldOccurrence::through(
        first_b.source,
        received,
    ))
    .unwrap();
    a.advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    b.advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let query = vec![phase(2, 0, 1), phase(0, 2, 1)];
    let x = a
        .advance(&mut NativeFieldOccurrence::entering(query.clone()))
        .unwrap();
    let y = b
        .advance(&mut NativeFieldOccurrence::entering(query))
        .unwrap();
    assert!(matches!(x.receiver, ConstitutiveReading::Unique { .. }));
    assert_eq!(x.receiver, y.receiver);
    for i in 0..2 {
        assert_eq!(turns[i].current().multiply(&x.outgoing[i]), y.outgoing[i]);
        assert_eq!(
            turns[i].current().multiply(&x.held_successor[i]),
            y.held_successor[i]
        );
    }
}

#[test]
#[ignore = "requires CUDA; status readout preserves the entire successor without copying its fibre"]
fn status_projection_keeps_full_native_successor_and_avoids_basis_readout() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut full = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let mut projected = NativeConstitutiveField::found(&surface, equal_seed(2)).unwrap();
    let f = full
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let p = projected
        .advance_status(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let actual = vec![phase(2, 0, 1), phase(0, 4, 1)];
    full.advance(&mut NativeFieldOccurrence::through(
        f.source,
        actual.clone(),
    ))
    .unwrap();
    projected
        .advance_status(&mut NativeFieldOccurrence::through(p.source, actual))
        .unwrap();
    full.advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    projected
        .advance_status(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let before = full.census();
    let f = full
        .advance(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let after = full.census();
    let full_octets = after.egress_section_octets - before.egress_section_octets;
    let before = projected.census();
    let p = projected
        .advance_status(&mut NativeFieldOccurrence::entering(zero(2)))
        .unwrap();
    let after = projected.census();
    let projected_octets = after.egress_section_octets - before.egress_section_octets;
    assert!(matches!(f.receiver, ConstitutiveReading::Plural { .. }));
    assert_eq!(p.receiver, NativeFieldReceiverStatus::Plural);
    assert_eq!(full_octets - projected_octets, 12 * 12 * 16);
    assert_eq!(after.section_read_outs - before.section_read_outs, 1);
    assert_eq!(f.lineage, p.lineage);
    assert_eq!(f.outgoing, p.outgoing);
    assert_eq!(f.held_successor, p.held_successor);
    assert_eq!(
        full.inspect_relation().unwrap(),
        projected.inspect_relation().unwrap()
    );
    assert_eq!(
        full.inspect_held().unwrap(),
        projected.inspect_held().unwrap()
    );
    for i in 0..full.occurrence_count() {
        assert_eq!(
            full.inspect_source(i).unwrap(),
            projected.inspect_source(i).unwrap()
        );
        assert_eq!(full.lineage(i), projected.lineage(i));
    }
}
