use super::super::tests::{material, phase};
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn capture(
    body: &NativeConstitutiveEcology<'_>,
    handles: &[Option<NativeEmissionHandle>],
) -> NativeEcologyRest {
    body.rest(&handles.iter().map(Option::as_ref).collect::<Vec<_>>())
        .unwrap()
}
fn wire(rest: &NativeEcologyRest) -> Vec<u8> {
    let mut bytes = Vec::new();
    rest.write(&mut bytes).unwrap();
    bytes
}
fn read(bytes: &[u8]) -> NativeEcologyRest {
    NativeEcologyRest::read(&mut &*bytes, bytes.len() as u64).unwrap()
}

fn develop(body: &mut NativeConstitutiveEcology<'_>) -> Vec<Option<NativeEmissionHandle>> {
    let a = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let b = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(0, 1, 1)))
        .unwrap();
    body.rechart(&[phase(0, 1, 1), phase(1, 0, 1)]).unwrap();
    let dropped = body
        .advance(&mut NativeCurrentOccurrence::through(
            a.source,
            phase(1, 0, 1),
        ))
        .unwrap();
    body.replace_incoming_transport(0, phase(-1, 0, 1)).unwrap();
    let last = body
        .advance(&mut NativeCurrentOccurrence::through(
            b.source,
            phase(0, 1, 1),
        ))
        .unwrap();
    body.rechart(&[phase(0, -1, 1), phase(1, 0, 1)]).unwrap();
    drop(dropped); // Its unreturned emission must NOT recreate a handle after rest.
    vec![None, None, None, None, Some(last.source)] // slot 4 deliberately refers to native occurrence 3
}

#[test]
#[ignore = "requires CUDA; whole native state and history remount without replay"]
fn whole_rest_preserves_sections_frames_material_and_continued_development() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut reference = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut reference_handles = develop(&mut reference);
    let mut original = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let handles = develop(&mut original);
    let rest = capture(&original, &handles);
    assert_eq!(rest, capture(&reference, &reference_handles));
    assert_eq!(rest.source_slots(), &[None, None, None, None, Some(3)]);
    let bytes = wire(&rest);
    let census = surface.census();
    drop(original);
    drop(handles);
    drop(rest);
    let (mut restored, mut restored_handles) =
        NativeConstitutiveEcology::remount(&surface, read(&bytes)).unwrap();
    assert_eq!(
        surface.census().deed_launches,
        census.deed_launches,
        "remount must not replay native deeds"
    );
    assert_eq!(wire(&capture(&restored, &restored_handles)), bytes);
    for i in 0..3 {
        assert_eq!(
            restored.joined_incidence(i, i + 1).unwrap().len(),
            reference.joined_incidence(i, i + 1).unwrap().len()
        );
        for (a, b) in restored
            .joined_incidence(i, i + 1)
            .unwrap()
            .into_iter()
            .zip(reference.joined_incidence(i, i + 1).unwrap())
        {
            assert_eq!(a.first.source.position, b.first.source.position);
            assert_eq!(a.first.target.position, b.first.target.position);
            assert_eq!(a.second.source.position, b.second.source.position);
            assert_eq!(a.second.target.position, b.second.target.position);
            assert_eq!(a.first.transport, b.first.transport);
            assert_eq!(a.second.transport, b.second.transport);
            assert_eq!(a.middle_transport, b.middle_transport);
        }
    }
    let mut r = reference_handles[4].take().unwrap();
    let mut s = restored_handles[4].take().unwrap();
    for arriving in [phase(2, -1, 3), phase(-1, 2, 3)] {
        let before = reference
            .advance(&mut NativeCurrentOccurrence::through(r, arriving))
            .unwrap();
        let after = restored
            .advance(&mut NativeCurrentOccurrence::through(s, arriving))
            .unwrap();
        assert_eq!(before.lineage, after.lineage);
        assert_eq!(before.source_currents, after.source_currents);
        assert_eq!(before.receiver, after.receiver);
        assert_eq!(before.received_difference, after.received_difference);
        assert_eq!(before.successor_rank, after.successor_rank);
        r = before.source;
        s = after.source;
    }
    assert_eq!(
        capture(&reference, &[Some(r)]),
        capture(&restored, &[Some(s)])
    );
}

#[test]
#[ignore = "requires CUDA; rest source handles remain actual and linear"]
fn rest_rejects_foreign_duplicate_handles_and_old_handles_remain_foreign_after_mount() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut a = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut b = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let x = a
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let y = b
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    assert!(a.rest(&[Some(&y.source)]).is_err());
    assert!(a.rest(&[Some(&x.source), Some(&x.source)]).is_err());
    let (mut c, mut handles) =
        NativeConstitutiveEcology::remount(&surface, a.rest(&[Some(&x.source)]).unwrap()).unwrap();
    assert!(c
        .advance(&mut NativeCurrentOccurrence::through(
            x.source,
            phase(1, 0, 1)
        ))
        .is_err());
    assert_eq!(c.occurrence_count(), 1);
    c.advance(&mut NativeCurrentOccurrence::through(
        handles[0].take().unwrap(),
        phase(1, 0, 1),
    ))
    .unwrap();
    assert_eq!(c.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; uncertainty cannot be published as confirmed native state"]
fn uncertain_native_body_cannot_produce_a_remountable_rest() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    body.relation.usable = false; // fault at the actual uncertainty boundary
    let before = surface.census();
    assert!(matches!(body.rest(&[]), Err(Error::Uncertain)));
    assert_eq!(surface.census(), before);
}

#[test]
#[ignore = "requires CUDA; malformed rest rejects before any native mount"]
fn malformed_lineage_frames_handles_and_sections_are_refused_without_effects() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let handles = develop(&mut body);
    let bytes = wire(&capture(&body, &handles));
    let before = surface.census();
    let corruptions: Vec<Box<dyn Fn(&mut NativeEcologyRest)>> = vec![
        Box::new(|r| r.header.materials.push(r.header.materials[0].clone())),
        Box::new(|r| r.header.history[2].lineage.received_from = Some(3)),
        Box::new(|r| r.header.history[0].returned = false),
        Box::new(|r| r.header.history[2].frame = 0),
        Box::new(|r| r.header.frames[1].root_to_local[0] = phase(1, 0, 1)),
        Box::new(|r| r.header.source_slots[0] = Some(3)),
        Box::new(|r| r.header.source_slots[4] = Some(0)),
        Box::new(|r| r.seed.intervals[0] = (99, 99)),
        Box::new(|r| r.memory.intervals[2] = (0, 0)),
        Box::new(|r| r.basis.intervals[0] = (-1, -1)),
        Box::new(|r| r.emissions[0].intervals[4] = (0, 0)),
        Box::new(|r| r.header.changes[0].node = 99),
        Box::new(|r| r.header.recharts[0].at_state = Some(999)),
    ];
    for corrupt in corruptions {
        let mut rest = read(&bytes);
        corrupt(&mut rest);
        assert!(NativeConstitutiveEcology::remount(&surface, rest).is_err());
    }
    assert_eq!(surface.census(), before);
    for at in [0, 1, MAGIC.len(), bytes.len() / 2, bytes.len() - 1] {
        assert!(NativeEcologyRest::read(&mut &bytes[..at], at as u64).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(NativeEcologyRest::read(&mut &trailing[..], trailing.len() as u64).is_err());
    let mut hostile = bytes.clone();
    hostile[MAGIC.len()..MAGIC.len() + 8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(NativeEcologyRest::read(&mut &hostile[..], hostile.len() as u64).is_err());
}

#[test]
#[ignore = "requires CUDA; zero-history rechart and physical changes retain their frame history"]
fn empty_body_and_changes_before_first_occurrence_roundtrip() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let empty = wire(&body.rest(&[]).unwrap());
    assert_eq!(read(&empty).rank(), 0);
    body.replace_incoming_transport(0, phase(-1, 0, 1)).unwrap();
    body.rechart(&[phase(0, 1, 1), phase(1, 0, 1)]).unwrap();
    body.replace_incoming_transport(1, phase(-1, 0, 1)).unwrap();
    let bytes = wire(&body.rest(&[]).unwrap());
    drop(body);
    let (mut restored, handles) =
        NativeConstitutiveEcology::remount(&surface, read(&bytes)).unwrap();
    assert!(handles.is_empty());
    assert_eq!(wire(&restored.rest(&[]).unwrap()), bytes);
    assert_eq!(
        restored
            .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
            .unwrap()
            .lineage
            .frame,
        1
    );
}

#[test]
#[ignore = "requires CUDA; remount retains the complete plural fibre and old-frame comparison"]
fn plural_fibre_survives_rest_rechart_and_later_reception() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: phase(1, 0, 1),
        initial_held: phase(1, 0, 1),
    };
    let mut body = NativeConstitutiveEcology::found(&surface, vec![seed]).unwrap();
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
    let last = body
        .advance(&mut NativeCurrentOccurrence::through(
            second.source,
            phase(4, 0, 1),
        ))
        .unwrap();
    assert!(matches!(last.receiver, ConstitutiveReading::Plural { .. }));
    body.rechart(&[phase(3, 4, 5)]).unwrap();
    let bytes = wire(&body.rest(&[Some(&last.source)]).unwrap());
    drop(body);
    drop(last);
    let (mut restored, mut handles) =
        NativeConstitutiveEcology::remount(&surface, read(&bytes)).unwrap();
    assert_eq!(wire(&capture(&restored, &handles)), bytes);
    let step = restored
        .advance(&mut NativeCurrentOccurrence::through(
            handles[0].take().unwrap(),
            phase(5, 0, 1),
        ))
        .unwrap();
    match step.received_difference.unwrap().former_receiver_fibre {
        ConstitutiveReading::Plural { directions, .. } => assert_eq!(
            directions,
            vec![vec![
                Rat::from_integer(1.into()),
                Rat::from_integer(0.into())
            ]]
        ),
        other => panic!("remount collapsed the prior vertical fibre: {other:?}"),
    }
    assert!(matches!(step.receiver, ConstitutiveReading::Plural { .. }));
}
