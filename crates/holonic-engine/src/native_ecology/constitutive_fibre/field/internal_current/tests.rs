use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

pub(in super::super) fn mount<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
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
pub(in super::super) fn current<'a, 'c>(
    s: &'a ResidentSection<'c>,
) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::rational(s).unwrap()
}
pub(in super::super) fn seeds() -> Vec<NativeJunctionSeed> {
    vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }]
}
pub(in super::super) fn dark<'c>(
    s: &'c ResidentSurface<'c>,
    enclosed: bool,
    turn: NativePhaseCurrent,
) -> (NativeConstitutiveField<'c>, Vec<NativeFieldSourceAnchor>) {
    let mut b = if enclosed {
        NativeConstitutiveField::found_with_enclosed_junction(s, seeds(), ResidentGrain(72))
    } else {
        NativeConstitutiveField::found_with_paired_junction(s, seeds())
    }
    .unwrap();
    let one = mount(s, &[1, 0, 1]);
    let zero = mount(s, &[0, 0, 1]);
    let cancel = mount(s, &[-9, 0, 10]);
    let first = b
        .advance_current_resident(&mut NativeFieldOccurrence::entering(vec![]), current(&one))
        .unwrap();
    let source = b.retain_source(&first.source).unwrap();
    b.replace_incoming_transport(0, turn).unwrap();
    let mut born = Vec::new();
    for _ in 0..2 {
        let next = b
            .advance_current_resident(
                &mut NativeFieldOccurrence::through_anchor(&source, vec![]),
                current(&one),
            )
            .unwrap();
        born.push(b.retain_source(&next.source).unwrap());
    }
    b.advance_current_resident(
        &mut NativeFieldOccurrence::entering(vec![]),
        current(&cancel),
    )
    .unwrap();
    for _ in 0..2 {
        b.advance_current_resident(&mut NativeFieldOccurrence::entering(vec![]), current(&zero))
            .unwrap();
    }
    (b, born)
}

#[test]
#[ignore = "requires CUDA; internal phase hidden by a zero boundary supplies a learned generator"]
fn hidden_internal_phases_conduct_to_the_same_learned_relation() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut law = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    let zero = mount(&s, &[0, 0, 1]);
    for turn in [
        NativePhaseCurrent::unit(),
        NativePhaseCurrent::new(0, 1, 1).unwrap(),
    ] {
        let (mut body, births) = dark(&s, false, turn);
        let basis = body.inspect_relation().unwrap();
        let count = body.occurrence_count();
        let before = body.census();
        let a = body.read_internal_current(&births[0]).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        assert_eq!(body.census().ingress_octets, before.ingress_octets);
        assert_eq!(body.occurrence_count(), count);
        assert_eq!(body.inspect_relation().unwrap(), basis);
        let read = a.inspect().unwrap();
        assert_eq!(
            read.point_availability,
            NativeInternalPointAvailability::Exact
        );
        assert_eq!(
            read.current.center[0],
            turn.current().scaled(&Rat::new(1.into(), 3.into()))
        );
        let raw = body.inspect_junction(count - 1).unwrap().unwrap();
        assert!(
            raw.intervals[7..13]
                .iter()
                .chain(&raw.intervals[14..20])
                .all(|p| p.0 == 0 && p.1 == 0)
        );
        let direct = body.inspect_internal_currents().unwrap().unwrap();
        assert_eq!(read.contact, direct[0].contact);
        assert_eq!(read.current.center[0], direct[0].current);
        body.advance_current_resident(&mut NativeFieldOccurrence::entering(vec![]), current(&zero))
            .unwrap();
        let b = body.read_internal_current_at(1).unwrap();
        let before = body.census();
        law.advance_resident(a.current(), Some(b.current()))
            .unwrap();
        let predicted = law.advance_resident(b.current(), None).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        body.advance_current_resident(&mut NativeFieldOccurrence::entering(vec![]), current(&zero))
            .unwrap();
        let actual = body.read_internal_current(&births[0]).unwrap();
        let ConstitutiveReading::Unique { current: p } =
            predicted.inspect().unwrap().predecessor_reading
        else {
            panic!("generator remains open")
        };
        let actual = actual.inspect().unwrap();
        assert_eq!(
            p,
            vec![
                actual.current.center[0].real.clone(),
                actual.current.center[0].imaginary.clone()
            ]
        );
        assert_eq!(
            a.inspect().unwrap(),
            read,
            "later recurrence cannot rewrite the earlier source"
        );
    }
}

#[test]
#[ignore = "requires CUDA; prefix enclosures retain their actual error and cannot masquerade as point sources"]
fn enclosed_internal_receiver_keeps_the_phase_ball_and_refuses_point_use() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut body, births) = dark(&s, true, NativePhaseCurrent::new(0, 1, 1).unwrap());
    body.rechart(&[NativePhaseCurrent::new(3, 4, 5).unwrap()])
        .unwrap();
    let before = body.census();
    let returned = body.read_internal_current(&births[0]).unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    let read = returned.inspect().unwrap();
    let truth = body.inspect_internal_currents().unwrap().unwrap();
    assert_eq!(read.contact, truth[0].contact);
    assert!(read.current.contains(&[truth[0].current.clone()]));
    assert!(read.current.radius > Rat::zero());
    assert_eq!(
        read.point_availability,
        NativeInternalPointAvailability::NumericalEnclosure
    );
    let mut receiver = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    assert!(receiver.advance_resident(returned.current(), None).is_err());
    assert_eq!(receiver.occurrences(), 0);
    // A prefix subtracted from that SAME immutable prefix cancels its numerical error too.
    let (_, contact, report) = body.internal_current_section(2, 1).unwrap();
    let (_, same, availability) = inspect_sections(&s, &contact, &report).unwrap();
    assert_eq!(same.center, vec![ExactComplexWaveCurrent::zero()]);
    assert_eq!(same.radius, Rat::zero());
    assert_eq!(availability, NativeInternalPointAvailability::Exact);
}

#[test]
#[ignore = "requires CUDA; internal source scope and archive placement preserve the actual contact"]
fn internal_receiver_keeps_scope_and_archived_births() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut body, births) = dark(&s, false, NativePhaseCurrent::unit());
    let (other, foreign) = dark(&s, false, NativePhaseCurrent::unit());
    assert!(body.read_internal_current(&foreign[0]).is_err());
    assert!(body.read_internal_current_at(0).is_err());
    assert!(body.read_internal_current_at(99).is_err());
    let expected = body
        .read_internal_current(&births[0])
        .unwrap()
        .inspect()
        .unwrap();
    let path = std::env::temp_dir().join(format!(
        "holonics-internal-current-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    body.enable_history_archive(&path).unwrap();
    body.archive_history_before(body.occurrence_count())
        .unwrap();
    assert_eq!(
        body.read_internal_current(&births[0])
            .unwrap()
            .inspect()
            .unwrap(),
        expected
    );
    let mut bytes = Vec::new();
    body.rest(&[], &[]).unwrap().write(&mut bytes).unwrap();
    let rest = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    drop(body);
    drop(other);
    let (mut restored, _, _) = NativeConstitutiveField::remount(&s, rest).unwrap();
    assert_eq!(
        restored
            .read_internal_current_at(1)
            .unwrap()
            .inspect()
            .unwrap(),
        expected
    );
    drop(restored);
    std::fs::remove_file(path).unwrap();
}
