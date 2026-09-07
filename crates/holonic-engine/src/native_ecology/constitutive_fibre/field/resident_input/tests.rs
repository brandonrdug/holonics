use super::*;
use crate::embedding_fiber::ResidentReadout;
fn seeds(n: usize) -> Vec<NativeJunctionSeed> {
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
fn mount<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            v.len(),
            ResidentGrain(0),
            64,
            v.iter().map(|x| (*x, *x)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::rational(s).unwrap()
}
fn phases(v: &[i64]) -> Vec<NativePhaseCurrent> {
    let den = *v.last().unwrap();
    v[..v.len() - 1]
        .chunks_exact(2)
        .map(|x| NativePhaseCurrent::new(x[0], x[1], den).unwrap())
        .collect()
}
fn path() -> std::path::PathBuf {
    std::env::temp_dir().join(format!(
        "holonics-resident-input-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}

#[test]
#[ignore = "requires CUDA; resident rational input preserves archive/rest provenance and continuation"]
fn resident_rational_input_archive_rest_remount_continues_the_same_enclosed_field() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let inputs = [[3, 4, -2, 1, 5], [1, -3, 2, 2, 7], [0, 2, -1, 1, 3]];
    let turn = NativePhaseCurrent::new(0, 1, 1).unwrap();
    let mut reference = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seeds(2),
        ResidentGrain(72),
    )
    .unwrap();
    let mut persisted = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seeds(2),
        ResidentGrain(72),
    )
    .unwrap();
    let archive = path();
    persisted.enable_history_archive(&archive).unwrap();

    let mut reference_first = NativeFieldOccurrence::entering(vec![]);
    let reference_first = reference
        .advance_current_resident(&mut reference_first, current(&mount(&surface, &inputs[0])))
        .unwrap();
    assert!(reference_first.lineage.incoming.is_resident());
    let reference_anchor = reference.retain_source(&reference_first.source).unwrap();
    let mut reference_second = NativeFieldOccurrence::through(reference_first.source, vec![]);
    let reference_second = reference
        .advance_current_resident(&mut reference_second, current(&mount(&surface, &inputs[1])))
        .unwrap();
    assert!(reference_second.lineage.incoming.is_resident());

    let mut persisted_first = NativeFieldOccurrence::entering(vec![]);
    let persisted_first = persisted
        .advance_current_resident(&mut persisted_first, current(&mount(&surface, &inputs[0])))
        .unwrap();
    assert!(persisted_first.lineage.incoming.is_resident());
    let persisted_anchor = persisted.retain_source(&persisted_first.source).unwrap();
    let mut persisted_second = NativeFieldOccurrence::through(persisted_first.source, vec![]);
    let persisted_second = persisted
        .advance_current_resident(&mut persisted_second, current(&mount(&surface, &inputs[1])))
        .unwrap();
    assert!(persisted_second.lineage.incoming.is_resident());
    persisted.archive_history_before(1).unwrap();
    assert_eq!(persisted.history_placement().archived_occurrences, 1);

    let turns = vec![turn; 2];
    reference.rechart(&turns).unwrap();
    persisted.rechart(&turns).unwrap();
    for at in 0..2 {
        assert_eq!(reference.inspect_incoming(at).unwrap(), phases(&inputs[at]));
        assert_eq!(persisted.inspect_incoming(at).unwrap(), phases(&inputs[at]));
        assert_eq!(
            reference.inspect_junction(at).unwrap(),
            persisted.inspect_junction(at).unwrap()
        );
    }
    assert_eq!(
        reference.inspect_internal_currents().unwrap(),
        persisted.inspect_internal_currents().unwrap()
    );
    let reference_wire = reference.rest(&[], &[Some(&reference_anchor)]).unwrap();
    let persisted_wire = persisted.rest(&[], &[Some(&persisted_anchor)]).unwrap();
    assert_eq!(reference_wire, persisted_wire);
    let mut bytes = Vec::new();
    persisted_wire.write(&mut bytes).unwrap();
    let decoded = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(decoded, persisted_wire);
    drop(persisted);

    let (mut resumed, sources, anchors) =
        NativeConstitutiveField::remount(&surface, decoded).unwrap();
    assert!(sources.is_empty());
    assert_eq!(anchors.len(), 1);
    for at in 0..2 {
        assert_eq!(resumed.inspect_incoming(at).unwrap(), phases(&inputs[at]));
        assert_eq!(
            resumed.inspect_junction(at).unwrap(),
            reference.inspect_junction(at).unwrap()
        );
    }
    assert_eq!(
        resumed.inspect_internal_currents().unwrap(),
        reference.inspect_internal_currents().unwrap()
    );

    let mut reference_late = NativeFieldOccurrence::through_anchor(&reference_anchor, vec![]);
    let reference_late = reference
        .advance_current_resident(&mut reference_late, current(&mount(&surface, &inputs[2])))
        .unwrap();
    assert!(reference_late.lineage.incoming.is_resident());
    let mut resumed_late =
        NativeFieldOccurrence::through_anchor(anchors[0].as_ref().unwrap(), vec![]);
    let resumed_late = resumed
        .advance_current_resident(&mut resumed_late, current(&mount(&surface, &inputs[2])))
        .unwrap();
    assert!(resumed_late.lineage.incoming.is_resident());
    assert_eq!(reference_late.lineage, resumed_late.lineage);
    assert_eq!(resumed.inspect_incoming(2).unwrap(), phases(&inputs[2]));
    assert_eq!(reference.inspect_incoming(2).unwrap(), phases(&inputs[2]));
    assert_eq!(
        resumed.inspect_junction(2).unwrap(),
        reference.inspect_junction(2).unwrap()
    );
    assert_eq!(
        resumed.inspect_internal_currents().unwrap(),
        reference.inspect_internal_currents().unwrap()
    );
    assert_eq!(
        resumed.rest(&[], &[]).unwrap(),
        reference.rest(&[], &[]).unwrap()
    );
    drop(reference_second);
    drop(persisted_second);
    drop(reference_late);
    drop(resumed_late);
    std::fs::remove_file(archive).unwrap();
}

#[test]
#[ignore = "requires CUDA; generated ingress obeys the same paired recurrence through delayed sources and rechart"]
fn resident_input_and_exterior_input_produce_the_same_complete_field() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    for enclosed in [false, true] {
        let found = || {
            if enclosed {
                NativeConstitutiveField::found_with_enclosed_junction(
                    &s,
                    seeds(2),
                    ResidentGrain(72),
                )
                .unwrap()
            } else {
                NativeConstitutiveField::found_with_paired_junction(&s, seeds(2)).unwrap()
            }
        };
        let mut native = found();
        let mut exterior = found();
        let mut ns = Vec::<Option<NativeFieldEmission>>::new();
        let mut es = Vec::<Option<NativeFieldEmission>>::new();
        for (at, words) in [
            [3, 4, -2, 1, 5],
            [1, 0, 0, 1, 1],
            [2, -1, 1, 3, 2],
            [0, 2, -3, 1, 3],
        ]
        .iter()
        .enumerate()
        {
            if at == 2 {
                let turns = vec![
                    NativePhaseCurrent::new(0, 1, 1).unwrap(),
                    NativePhaseCurrent::new(0, -1, 1).unwrap(),
                ];
                native.rechart(&turns).unwrap();
                exterior.rechart(&turns).unwrap();
            }
            let input = mount(&s, words);
            let link = if at < 2 { None } else { Some(at - 2) };
            let mut n = match link {
                Some(i) => NativeFieldOccurrence::through(ns[i].take().unwrap(), vec![]),
                None => NativeFieldOccurrence::entering(vec![]),
            };
            let mut e = match link {
                Some(i) => NativeFieldOccurrence::through(es[i].take().unwrap(), phases(words)),
                None => NativeFieldOccurrence::entering(phases(words)),
            };
            let before = native.census();
            let next = native.advance_current_resident(&mut n, current(&input));
            assert_eq!(native.census().section_read_outs, before.section_read_outs);
            assert_eq!(native.census().ingress_octets - before.ingress_octets, 4);
            let other = exterior.advance_resident(&mut e);
            if let (Err(a), Err(b)) = (&next, &other) {
                // Keep the word-realization limit visible. The enclosed realization must finish
                // the complete same sequence, not hide the refused inputs or enlarge a word cap.
                assert!(!enclosed && at >= 2, "unexpected refusal at {at}: {a}; {b}");
                assert!(matches!(a, ConstitutiveFibreError::Arithmetic(_)));
                assert!(matches!(b, ConstitutiveFibreError::Arithmetic(_)));
                assert!(n.source_ref().is_some() && e.source_ref().is_some());
                assert_eq!(native.occurrence_count(), at);
                assert_eq!(exterior.occurrence_count(), at);
                assert_eq!(
                    native.inspect_held().unwrap(),
                    exterior.inspect_held().unwrap()
                );
                assert_eq!(
                    native.inspect_relation().unwrap(),
                    exterior.inspect_relation().unwrap()
                );
                eprintln!(
                    "both rational-word input routes refuse at occurrence {at}: native={a}; exterior={b}"
                );
                break;
            }
            let next =
                next.unwrap_or_else(|e| panic!("resident at {at}, enclosed={enclosed}: {e}"));
            let other =
                other.unwrap_or_else(|e| panic!("exterior at {at}, enclosed={enclosed}: {e}"));
            assert!(next.lineage.incoming.is_resident());
            ns.push(Some(next.source));
            es.push(Some(other.source));
            assert_eq!(native.inspect_incoming(at).unwrap(), phases(words));
            assert_eq!(
                native.inspect_held().unwrap(),
                exterior.inspect_held().unwrap()
            );
            assert_eq!(
                native.inspect_relation().unwrap(),
                exterior.inspect_relation().unwrap()
            );
            assert_eq!(
                native.inspect_junction(at).unwrap(),
                exterior.inspect_junction(at).unwrap()
            );
        }
        assert_eq!(
            native.inspect_internal_currents().unwrap(),
            exterior.inspect_internal_currents().unwrap()
        );
        if enclosed {
            assert_eq!(native.occurrence_count(), 4);
        }
    }
}

#[test]
#[ignore = "requires CUDA; malformed/foreign/plural input refuses before the field consumes a source"]
fn refused_native_input_keeps_the_original_field_and_source_capability() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let other = ResidentSurface::on(&r).unwrap();
    let mut field = NativeConstitutiveField::found_with_paired_junction(&s, seeds(1)).unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let mut occurrence = NativeFieldOccurrence::through(first.source, vec![]);
    let held = field.inspect_held().unwrap();
    let relation = field.inspect_relation().unwrap();
    let bad = mount(&s, &[1, 0, 0]);
    let foreign = mount(&other, &[1, 0, 1]);
    for input in [&bad, &foreign] {
        assert!(
            field
                .advance_current_resident(&mut occurrence, current(input))
                .is_err()
        );
        assert!(occurrence.source_ref().is_some());
        assert_eq!(field.occurrence_count(), 1);
        assert_eq!(field.inspect_held().unwrap(), held);
        assert_eq!(field.inspect_relation().unwrap(), relation);
    }
    let mut action = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    action.advance(&[0, 0], Some(&[1, 0])).unwrap();
    let z = mount(&s, &[0, 0, 1]);
    let plural = action.advance_resident(current(&z), None).unwrap();
    assert!(
        field
            .advance_current_resident(&mut occurrence, plural.current())
            .is_err()
    );
    assert!(occurrence.source_ref().is_some());
    assert_eq!(field.occurrence_count(), 1);
    let good = mount(&s, &[3, 4, 5]);
    let next = field
        .advance_current_resident(&mut occurrence, current(&good))
        .unwrap();
    assert!(occurrence.source_ref().is_none());
    assert_eq!(next.lineage.received_from, Some(0));
    let mut ambiguous =
        NativeFieldOccurrence::through(next.source, vec![NativePhaseCurrent::unit()]);
    assert!(
        field
            .advance_current_resident(&mut ambiguous, current(&good))
            .is_err()
    );
    assert!(ambiguous.source_ref().is_some());
    assert_eq!(field.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; resident input survives archive, exact internal/material decoding and cold restart"]
fn resident_input_persists_and_complete_current_decoders_use_its_actual_carrier() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seeds(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let mut prefix = NativeCurrentHistorySourceReceiver::on_empty(&body).unwrap();
    let p = path();
    body.enable_history_archive(&p).unwrap();
    let mut source = None;
    let mut expected = Vec::new();
    for words in [[1, 0, 1], [0, 1, 1], [1, 1, 1], [-1, 0, 1]] {
        let input = mount(&s, &words);
        let mut occurrence = source.take().map_or_else(
            || NativeFieldOccurrence::entering(vec![]),
            |s| NativeFieldOccurrence::through(s, vec![]),
        );
        let before = body.census();
        let next = body
            .advance_current_resident(&mut occurrence, current(&input))
            .unwrap();
        let complete = prefix.receive_completed(&body).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        assert_eq!(body.census().ingress_octets - before.ingress_octets, 4);
        expected.push(phases(&words));
        source = Some(next.source);
        prefix.inspect(&complete).unwrap();
    }
    let exact = body.inspect_exact_complete_material_transport(3).unwrap();
    let before = body.rest(&[source.as_ref()], &[]).unwrap();
    body.archive_history_before(4).unwrap();
    for (at, input) in expected.iter().enumerate() {
        assert_eq!(&body.inspect_incoming(at).unwrap(), input);
    }
    assert_eq!(
        body.inspect_exact_complete_material_transport(3).unwrap(),
        exact
    );
    assert_eq!(body.rest(&[source.as_ref()], &[]).unwrap(), before);
    let mut bytes = Vec::new();
    before.write(&mut bytes).unwrap();
    let restored = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(restored, before);
    drop(prefix);
    drop(source);
    drop(body);
    let count = s.census().deed_launches;
    let (mut resumed, mut sources, _) = NativeConstitutiveField::remount(&s, restored).unwrap();
    assert_eq!(s.census().deed_launches, count);
    for (at, input) in expected.iter().enumerate() {
        assert_eq!(&resumed.inspect_incoming(at).unwrap(), input);
    }
    assert_eq!(
        resumed
            .inspect_exact_complete_material_transport(3)
            .unwrap(),
        exact
    );
    let input = mount(&s, &[0, -1, 1]);
    let mut occurrence = NativeFieldOccurrence::through(sources[0].take().unwrap(), vec![]);
    resumed
        .advance_current_resident(&mut occurrence, current(&input))
        .unwrap();
    resumed
        .inspect_exact_complete_material_transport(4)
        .unwrap();
    drop(resumed);
    std::fs::remove_file(p).unwrap();
}

#[test]
fn exterior_input_wire_stays_compatible_and_resident_metadata_is_strict() {
    let values = vec![NativePhaseCurrent::unit()];
    let old = serde_json::to_value(&values).unwrap();
    assert_eq!(
        serde_json::to_value(NativeFieldIncoming::Exterior(values.clone())).unwrap(),
        old
    );
    assert_eq!(
        serde_json::from_value::<NativeFieldIncoming>(old).unwrap(),
        NativeFieldIncoming::Exterior(values)
    );
    assert!(
        serde_json::from_value::<NativeFieldIncoming>(
            serde_json::json!({"resident_nodes":1,"unknown":true})
        )
        .is_err()
    );
}
