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
#[ignore = "requires CUDA; a current-difference generator keeps the actual observed source"]
fn current_difference_wire_rejects_a_different_causal_source() {
    let readout=ResidentReadout::new().unwrap();
    let surface=ResidentSurface::on(&readout).unwrap();
    let mut field=NativeConstitutiveField::found_with_enclosed_junction(&surface,seed(),ResidentGrain(72)).unwrap();
    field.enable_material_transport_source(NativeMaterialTransportSource::OperativeLinear).unwrap();
    let mut last=None;
    for value in [1,2,3] {
        let mut event=match last.take(){Some(source)=>NativeFieldOccurrence::through(source,vec![phase(value)]),None=>NativeFieldOccurrence::entering(vec![phase(value)])};
        last=Some(field.advance_resident(&mut event).unwrap().source);
    }
    let query=field.pull_back_material_current(2).unwrap().unwrap();
    let response=field.material_contact_response(query).unwrap();
    field.apply_material_contact_realization(&response,NativeContactRealization::DyadicDeposit).unwrap();
    let mut rest=field.rest(&[last.as_ref()],&[]).unwrap();
    assert_eq!(rest.header.operative.as_ref().unwrap().return_frames[0].current_difference_source,Some(1));
    rest.header.operative.as_mut().unwrap().return_frames[0].current_difference_source=Some(0);
    assert!(rest.validate().unwrap_err().to_string().contains("current-factor source lineage"));
    rest.header.operative.as_mut().unwrap().return_frames[0].current_difference_source=Some(1);
    rest.validate().unwrap();
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
        assert!(bytes.starts_with(MAGIC));
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

#[test]
#[ignore = "requires CUDA; joint current codec validates actual w/b and an empty observation history"]
fn joint_image_rest_matches_outgoing_and_rejects_corruption_without_history() {
    let readout=ResidentReadout::new().unwrap();
    let surface=ResidentSurface::on(&readout).unwrap();
    let mut field=NativeConstitutiveField::found_with_enclosed_junction(&surface,seed(),ResidentGrain(48)).unwrap();
    field.enable_operative_contacts().unwrap();
    let source=field.read_current_source().unwrap();
    let point=surface.mount_section_rest(&ResidentSectionRest::found(1,6,ResidentGrain(0),64,
        vec![(1,1),(2,2),(3,3),(4,4),(5,5),(6,6)]).unwrap()).unwrap();
    let input=ResidentNormalInput::Point(ResidentConstitutiveCurrent::integers(&point).unwrap())
        .enclosure(&surface,ResidentGrain(48)).unwrap();
    let reflection=source.reflect(input.view()).unwrap();
    let expected=reflection.output().inspect().unwrap();
    field.commit_reflection(&reflection).unwrap();
    let mut rest=field.rest(&[],&[]).unwrap();
    assert!(rest.current_junction.is_none());
    assert!(rest.joint_current.is_some());
    let mut bytes=Vec::new();rest.write(&mut bytes).unwrap();
    assert!(bytes.starts_with(JOINT_MAGIC));
    let saved=NativeFieldRest::read(&mut bytes.as_slice(),bytes.len() as u64).unwrap();
    let (mut resumed,_,_)=NativeConstitutiveField::remount(&surface,saved).unwrap();
    assert_eq!(resumed.read_current_source().unwrap().enclosure().inspect().unwrap(),expected);
    let image=rest.joint_current.as_mut().unwrap();
    let first=image.intervals[0];image.intervals[0]=(first.0+1,first.1+1);
    assert!(rest.validate().unwrap_err().to_string().contains("joint image disagrees"));
    rest.joint_current.as_mut().unwrap().intervals[0]=first;
    let image=rest.joint_current.as_mut().unwrap();
    let end=image.intervals.len();
    image.intervals[end-2]=(-1,-1);image.intervals[end-1]=(-1,-1);
    assert!(rest.validate().unwrap_err().to_string().contains("joint image extent/radius"));
}

/// Phase 8b retention bound. A source-only field — the owner every incident and generator-machine
/// body founds (`found_incident_source_only`) — has no occurrence clock: the legacy advance is
/// refused at runtime, its rest carries no history, and a legacy occurrence grafted onto its wire
/// is refused by validation rather than mounted.
#[test]
#[ignore = "requires CUDA; a source-only field refuses occurrences at runtime and at rest"]
fn source_only_field_refuses_occurrences_at_runtime_and_at_rest() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_incident_source_only(&surface, seed(), ResidentGrain(48))
            .unwrap();
    let refused = field.advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]));
    assert!(
        matches!(&refused, Err(ConstitutiveFibreError::Rest(m)) if m.contains("no legacy constitutive advance"))
    );
    assert_eq!(field.occurrence_count(), 0);
    let rest = field.rest(&[], &[]).unwrap();
    assert_eq!(rest.occurrences(), 0);
    let mut bytes = Vec::new();
    rest.write(&mut bytes).unwrap();
    let decoded = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    let (mut resumed, sources, anchors) =
        NativeConstitutiveField::remount(&surface, decoded).unwrap();
    assert_eq!(resumed.occurrence_count(), 0);
    assert!(sources.is_empty() && anchors.is_empty());
    // Source-only fields still have no legacy occurrence history after ordinary remount.

    let mut legacy =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(48))
            .unwrap();
    legacy
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    let NativeFieldRest {
        header: legacy_header,
        history: legacy_history,
        ..
    } = legacy.rest(&[], &[]).unwrap();
    let mut grafted = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    grafted
        .header
        .history
        .extend(legacy_header.history.into_iter().take(1));
    grafted.history.extend(legacy_history.into_iter().take(1));
    grafted.initial_junction = None;
    assert!(
        grafted
            .validate()
            .unwrap_err()
            .to_string()
            .contains("source-only field has legacy history")
    );
}

fn two_node_seed() -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        2
    ]
}

fn two_node_input(n: i64) -> Vec<NativePhaseCurrent> {
    vec![
        NativePhaseCurrent::new(n, 1, 1).unwrap(),
        NativePhaseCurrent::new(1, -n, 1).unwrap(),
    ]
}

fn develop_resident_history(body: &mut NativeConstitutiveField<'_>) {
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(two_node_input(1)))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    let mut source = first.source;
    for at in 1..12 {
        if at == 3 {
            body.rechart(&[
                NativePhaseCurrent::new(0, 1, 1).unwrap(),
                NativePhaseCurrent::new(-1, 0, 1).unwrap(),
            ])
            .unwrap();
        }
        if at == 8 {
            body.replace_incoming_transport(1, NativePhaseCurrent::new(0, -1, 1).unwrap())
                .unwrap();
        }
        let mut occurrence = if at == 4 || at == 10 {
            NativeFieldOccurrence::through_anchor(&anchor, two_node_input(at + 1))
        } else {
            NativeFieldOccurrence::through(source, two_node_input(at + 1))
        };
        let before = body.census();
        source = body.advance_resident(&mut occurrence).unwrap().source;
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
    }
}

#[test]
#[ignore = "requires CUDA; resident history preserves frames, delayed sources, material and ordinary rest"]
fn resident_history_returns_the_same_current_and_cold_rest() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut reference = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        two_node_seed(),
        ResidentGrain(72),
    )
    .unwrap();
    reference.enable_material_transport().unwrap();
    develop_resident_history(&mut reference);
    let expected = reference.rest(&[], &[]).unwrap();
    let expected_reading = reference.read_material_transport_pairs(0, 1).unwrap();
    drop(reference);

    let mut body = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        two_node_seed(),
        ResidentGrain(72),
    )
    .unwrap();
    body.enable_material_transport().unwrap();
    develop_resident_history(&mut body);
    assert_eq!(body.occurrence_count(), 12);
    assert_eq!(
        body.read_material_transport_pairs(0, 1).unwrap(),
        expected_reading
    );
    let rest = body.rest(&[], &[]).unwrap();
    assert_eq!(rest, expected);
    let mut bytes = Vec::new();
    rest.write(&mut bytes).unwrap();
    let decoded = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    drop(body);

    let before = surface.census();
    let (resumed, _, _) = NativeConstitutiveField::remount(&surface, decoded).unwrap();
    assert_eq!(surface.census().deed_launches, before.deed_launches);
    assert_eq!(resumed.occurrence_count(), 12);
    assert_eq!(resumed.rest(&[], &[]).unwrap(), expected);
    assert_eq!(
        resumed.read_material_transport_pairs(0, 1).unwrap(),
        expected_reading
    );
}
