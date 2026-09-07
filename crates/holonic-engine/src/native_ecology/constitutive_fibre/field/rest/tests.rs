use super::*;
use crate::embedding_fiber::ResidentReadout;

fn seed() -> Vec<NativeJunctionSeed> {
    vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }]
}
fn phase(a: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(a, 0, 1).unwrap()
}

#[test]
#[ignore = "requires CUDA; complete rest/remount continues the field and learned transport without replay"]
fn remount_preserves_current_coefficients_frames_and_live_capabilities() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport().unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    let second = body
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(2)],
        ))
        .unwrap();
    body.rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap()])
        .unwrap();
    body.replace_incoming_transport(0, NativePhaseCurrent::new(-1, 0, 1).unwrap())
        .unwrap();
    let state = body
        .rest(
            &[Some(&second.source), None],
            &[Some(&anchor), Some(&anchor)],
        )
        .unwrap();
    let mut bytes = Vec::new();
    state.write(&mut bytes).unwrap();
    let saved = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    assert_eq!(state, saved);
    drop(body);
    let mut reference =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    reference.enable_material_transport().unwrap();
    let reference_first = reference
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    let reference_anchor = reference.retain_source(&reference_first.source).unwrap();
    let _reference_second = reference
        .advance_resident(&mut NativeFieldOccurrence::through(
            reference_first.source,
            vec![phase(2)],
        ))
        .unwrap();
    reference
        .rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap()])
        .unwrap();
    reference
        .replace_incoming_transport(0, NativePhaseCurrent::new(-1, 0, 1).unwrap())
        .unwrap();
    reference
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &reference_anchor,
            vec![phase(3)],
        ))
        .unwrap();
    let expected = reference.rest(&[], &[]).unwrap();
    drop(reference);
    let (mut resumed, sources, anchors) =
        NativeConstitutiveField::remount(&surface, saved).unwrap();
    assert_eq!(resumed.occurrence_count(), 2);
    assert_eq!(sources.len(), 2);
    assert!(sources[1].is_none());
    let before = resumed.census();
    resumed
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            anchors[1].as_ref().unwrap(),
            vec![phase(3)],
        ))
        .unwrap();
    assert_eq!(resumed.census().deed_launches - before.deed_launches, 1);
    assert_eq!(expected, resumed.rest(&[], &[]).unwrap());
    let mut wrong = NativeFieldOccurrence::through(second.source, vec![phase(1)]);
    assert!(matches!(
        resumed.advance_resident(&mut wrong),
        Err(Error::ForeignOccurrence)
    ));
}

#[test]
#[ignore = "requires CUDA; rest authenticates explicit capability slots and rejects corrupt field wires"]
fn rest_does_not_regenerate_dropped_or_duplicate_capabilities() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveField::found(&surface, seed()).unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    assert!(body
        .rest(&[Some(&first.source), Some(&first.source)], &[])
        .is_err());
    let rest = body.rest(&[], &[]).unwrap();
    assert!(rest.source_slots().is_empty());
    let mut bytes = Vec::new();
    rest.write(&mut bytes).unwrap();
    assert!(NativeFieldRest::read(&mut &bytes[..bytes.len() - 1], bytes.len() as u64 - 1).is_err());
    let mut damaged = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    damaged.header.history[0].lineage.source_contact =
        Some(NativeFieldSourceContact::RetainedAnchor);
    assert!(damaged.validate().is_err());
    let mut damaged = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    damaged.header.anchor_slots.push(Some(3));
    assert!(damaged.validate().is_err());
}

#[test]
#[ignore = "requires CUDA; empty plain, exact and enclosed fields preserve their declared initial state"]
fn empty_field_variants_remount_without_an_initial_fake_occurrence() {
    for mode in 0..4 {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let mut body = match mode {
            0 => NativeConstitutiveField::found(&surface, seed()).unwrap(),
            1 => NativeConstitutiveField::found_with_paired_junction(&surface, seed()).unwrap(),
            _ => NativeConstitutiveField::found_with_enclosed_junction(
                &surface,
                seed(),
                ResidentGrain(72),
            )
            .unwrap(),
        };
        if mode == 3 {
            body.enable_material_transport().unwrap();
        }
        let rest = body.rest(&[], &[]).unwrap();
        let mut bytes = Vec::new();
        rest.write(&mut bytes).unwrap();
        drop(body);
        let decoded = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
        let (mut resumed, sources, anchors) =
            NativeConstitutiveField::remount(&surface, decoded).unwrap();
        assert_eq!(resumed.occurrence_count(), 0);
        assert!(sources.is_empty() && anchors.is_empty());
        assert_eq!(resumed.census().deed_launches, 0);
        resumed
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
            .unwrap();
        assert_eq!(resumed.occurrence_count(), 1);
        let mut malformed = rest;
        malformed.memory.intervals[0] = (1, 1);
        assert!(malformed.validate().is_err());
    }
}
