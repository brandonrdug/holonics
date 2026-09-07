use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn seed(n: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        n
    ]
}

#[test]
#[ignore = "requires CUDA; complete-current learning sees opposite internal currents behind zero boundary output"]
fn actual_return_learns_the_internal_direction_that_outgoing_only_cannot_see() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    for _ in 0..2 {
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![NativePhaseCurrent::unit()],
        ))
        .unwrap();
    }
    body.advance_resident(&mut NativeFieldOccurrence::entering(vec![
        NativePhaseCurrent::new(-9, 0, 10).unwrap(),
    ]))
    .unwrap();
    let mut sources = Vec::new();
    for _ in 0..3 {
        let next = body
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::zero(),
            ]))
            .unwrap();
        if body.occurrence_count() >= 6 {
            sources.push(body.retain_source(&next.source).unwrap());
        }
    }
    for at in [5, 6] {
        assert!(body
            .inspect_exact_junction(at)
            .unwrap()
            .unwrap()
            .outgoing
            .iter()
            .all(|v| v == &ExactComplexWaveCurrent::zero()));
    }
    body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &sources[0],
        vec![NativePhaseCurrent::unit()],
    ))
    .unwrap();
    let positive = body.read_complete_material_source(&sources[0]).unwrap();
    let negative = body.read_complete_material_source(&sources[1]).unwrap();
    assert!(&positive.center[0].real - &positive.radius > Rat::zero());
    assert!(&negative.center[0].real + &negative.radius < Rat::zero());
    for (ball, numerator) in [(&positive, 2), (&negative, -2)] {
        let truth =
            ExactComplexWaveCurrent::new(Rat::new(numerator.into(), 11.into()), Rat::zero());
        assert!(truth.subtract(&ball.center[0]).norm_square() <= &ball.radius * &ball.radius);
    }
    body.inspect_exact_complete_material_transport(7)
        .unwrap()
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; source-time, current-parameter and exact coefficient bounds survive complex phase and delayed return"]
fn full_transport_matches_its_exact_source_qualified_expression() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(2), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let mut latest = None;
    let mut anchor = None;
    for at in 0..6 {
        if at == 3 {
            body.rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap(); 2])
                .unwrap();
        }
        let input = vec![
            NativePhaseCurrent::new(at + 1, 1, 1).unwrap(),
            NativePhaseCurrent::new(2, 1 - at, 1).unwrap(),
        ];
        let mut occurrence = if at == 0 || at == 4 {
            NativeFieldOccurrence::entering(input)
        } else if at == 3 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else {
            NativeFieldOccurrence::through(latest.take().unwrap(), input)
        };
        let before = body.census();
        let next = body.advance_resident(&mut occurrence).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        if at == 0 {
            anchor = Some(body.retain_source(&next.source).unwrap());
        }
        latest = Some(next.source);
    }
    body.inspect_exact_complete_material_transport(5)
        .unwrap()
        .unwrap();
    let late = body
        .inspect_complete_material_transport(3)
        .unwrap()
        .unwrap();
    assert!(late
        .chronological_current
        .unwrap()
        .center
        .iter()
        .any(|v| v != &ExactComplexWaveCurrent::zero()));
    assert!(body.inspect_material_transport_state().is_err());
    let state = body
        .inspect_complete_material_transport_state()
        .unwrap()
        .unwrap();
    assert_eq!(state.birth_occurrences, 6);
}

#[test]
#[ignore = "requires CUDA; a complete-source refusal after encoder staging preserves the entire old owner"]
fn late_source_chart_refusal_keeps_old_field_coefficients_and_capability() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(1, 0, 2).unwrap(),
        ]))
        .unwrap();
    let before = body.rest(&[Some(&first.source)], &[]).unwrap();
    let mut incoming =
        NativeFieldOccurrence::through(first.source, vec![NativePhaseCurrent::unit()]);
    assert!(body.advance_resident(&mut incoming).is_err());
    assert_eq!(body.occurrence_count(), 1);
    let after = body.rest(&[incoming.source_ref()], &[]).unwrap();
    assert_eq!(before, after);
}

#[test]
#[ignore = "requires CUDA; complete source coefficients, birth moments and old-source expression continue after archived remount"]
fn complete_material_state_and_delayed_source_survive_archived_remount() {
    fn prefix(
        body: &mut NativeConstitutiveField<'_>,
    ) -> (NativeFieldEmission, NativeFieldSourceAnchor) {
        let first = body
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::unit(),
            ]))
            .unwrap();
        let anchor = body.retain_source(&first.source).unwrap();
        let second = body
            .advance_resident(&mut NativeFieldOccurrence::through(
                first.source,
                vec![NativePhaseCurrent::new(0, 1, 1).unwrap()],
            ))
            .unwrap();
        let third = body
            .advance_resident(&mut NativeFieldOccurrence::through(
                second.source,
                vec![NativePhaseCurrent::new(1, 1, 1).unwrap()],
            ))
            .unwrap();
        (third.source, anchor)
    }
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let (last, anchor) = prefix(&mut body);
    let saved = body.rest(&[Some(&last)], &[Some(&anchor)]).unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    drop(body);
    let mut reference =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    reference
        .enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let (_, reference_anchor) = prefix(&mut reference);
    reference
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &reference_anchor,
            vec![NativePhaseCurrent::new(2, -1, 1).unwrap()],
        ))
        .unwrap();
    let expected = reference.rest(&[], &[]).unwrap();
    drop(reference);
    let archive = std::env::temp_dir().join(format!(
        "holonics-complete-material-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let rest = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    let before = surface.census();
    let (mut resumed, _, anchors) =
        NativeConstitutiveField::remount_with_history_archive(&surface, rest, &archive).unwrap();
    assert_eq!(resumed.census().deed_launches, before.deed_launches);
    assert_eq!(
        resumed.material_transport_source(),
        Some(NativeMaterialTransportSource::CompleteCurrent)
    );
    resumed
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            anchors[0].as_ref().unwrap(),
            vec![NativePhaseCurrent::new(2, -1, 1).unwrap()],
        ))
        .unwrap();
    assert_eq!(resumed.rest(&[], &[]).unwrap(), expected);
    resumed
        .inspect_exact_complete_material_transport(3)
        .unwrap()
        .unwrap();
    drop(resumed);
    std::fs::remove_file(archive).unwrap();
}
