use super::super::internal_current::tests::{current, dark, mount, seeds};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

#[test]
#[ignore = "requires CUDA; a mode unfolds across arbitrary later forcing, new contacts and rechart"]
fn shared_drive_mode_cancels_future_forcing_before_numerical_projection() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut body, births) = dark(&s, true, NativePhaseCurrent::new(0, 1, 1).unwrap());
    let before = body.census();
    let mode = body.condense_shared_drive_mode(1, 2).unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.census().ingress_octets, before.ingress_octets);
    let origin = mode.unfold(0).unwrap().inspect().unwrap();
    assert_eq!(origin.receiving_occurrences, [1, 2]);
    assert_eq!(origin.source_occurrences, [0, 0]);
    let mut checked = Vec::new();
    for (i, words) in [
        [2, 1, 1],
        [-1, 2, 1],
        [0, 0, 1],
        [1, 0, 2],
        [-2, 0, 1],
        [0, 1, 1],
    ]
    .iter()
    .enumerate()
    {
        if i == 2 {
            body.rechart(&[NativePhaseCurrent::new(3, 4, 5).unwrap()])
                .unwrap();
        }
        if i == 3 {
            body.replace_incoming_transport(0, NativePhaseCurrent::new(0, -1, 1).unwrap())
                .unwrap();
        }
        let before = body.census();
        let predicted = mode.unfold(i as u64 + 1).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        assert_eq!(body.census().ingress_octets, before.ingress_octets);
        let input = mount(&s, words);
        let mut event = if i % 2 == 0 {
            NativeFieldOccurrence::through_anchor(&births[0], vec![])
        } else {
            NativeFieldOccurrence::entering(vec![])
        };
        body.advance_current_resident(&mut event, current(&input))
            .unwrap();
        let full = body.inspect_internal_currents().unwrap().unwrap();
        let truth = full[0].current.subtract(&full[1].current);
        let read = predicted.inspect().unwrap();
        assert!(read.current.contains(&[truth]));
        assert_eq!(
            read.current.radius, origin.current.radius,
            "the shared live prefix cancels, rather than adding its error"
        );
        let separate = body
            .read_internal_current_at(1)
            .unwrap()
            .inspect()
            .unwrap()
            .current
            .radius
            + body
                .read_internal_current_at(2)
                .unwrap()
                .inspect()
                .unwrap()
                .current
                .radius;
        assert!(read.current.radius <= separate);
        checked.push(read);
    }
    assert_eq!(mode.unfold(1).unwrap().inspect().unwrap(), checked[0]);
}

#[test]
#[ignore = "requires CUDA; generator plus amplitude persist without the source field or its raw history"]
fn a_restored_mode_generates_a_future_current_after_the_field_is_gone() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut body, births) = dark(&s, false, NativePhaseCurrent::unit());
    let mode = body.condense_shared_drive_mode(1, 2).unwrap();
    let mut bytes = Vec::new();
    mode.rest().unwrap().write(&mut bytes).unwrap();
    let expected = mode.unfold(u64::MAX).unwrap().inspect().unwrap();
    assert_eq!(
        expected.current.center[0].real,
        Rat::new((-2).into(), 3.into())
    );
    assert_eq!(expected.current.radius, Rat::zero());
    drop(mode);
    drop(births);
    drop(body);
    let rest = NativeSharedDriveModeRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let before = s.census();
    let restored = NativeSharedDriveMode::remount(&s, rest).unwrap();
    assert_eq!(s.census().deed_launches, before.deed_launches);
    let mut receiver = NativeConstitutiveField::found(&s, seeds()).unwrap();
    let before = s.census();
    let generated = restored.unfold(u64::MAX).unwrap();
    receiver
        .advance_current_resident(
            &mut NativeFieldOccurrence::entering(vec![]),
            generated.current(),
        )
        .unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(generated.inspect().unwrap(), expected);
    assert_eq!(
        receiver.inspect_incoming(0).unwrap(),
        vec![NativePhaseCurrent::new(-2, 0, 3).unwrap()]
    );
}

#[test]
#[ignore = "requires CUDA; shared source is not shared drive and an unsupported mode preserves the field"]
fn source_coincidence_does_not_supply_the_shared_drive_receipt() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seeds(), ResidentGrain(72))
            .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    for real in [1, 2] {
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![NativePhaseCurrent::new(real, 0, 1).unwrap()],
        ))
        .unwrap();
    }
    let old = body.rest(&[], &[]).unwrap();
    assert!(body.condense_shared_drive_mode(1, 2).is_err());
    assert!(body.condense_shared_drive_mode(1, 1).is_err());
    assert!(body.condense_shared_drive_mode(0, 2).is_err());
    assert_eq!(body.rest(&[], &[]).unwrap(), old);
}

#[test]
#[ignore = "requires CUDA; a mode wire cannot remove its numerical fibre by changing the point guard"]
fn mode_wire_keeps_the_declared_amplitude_fibre() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut body, _) = dark(&s, true, NativePhaseCurrent::unit());
    let mode = body.condense_shared_drive_mode(1, 2).unwrap();
    let mut rest = mode.rest().unwrap();
    let radius = material_transport::wides(&rest.amplitude.intervals[..8]).unwrap()[2];
    assert!(radius > 0);
    rest.amplitude.intervals[11] = (0, 0);
    assert!(NativeSharedDriveMode::remount(&s, rest).is_err());
}

#[test]
#[ignore = "requires native GPU; signed-wide mode wires preserve the point-port boundary"]
fn mode_unfold_preserves_wide_amplitudes_and_signed_word_boundaries() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut body, _) = dark(&s, false, NativePhaseCurrent::unit());
    let mode = body.condense_shared_drive_mode(1, 2).unwrap();
    // These are explicit cold wire controls, not amplitudes claimed to have been learned.
    for (wide, point, expected) in [
        (
            [i64::MIN as i128, i64::MAX as i128, 0, 1],
            [i64::MIN, i64::MAX, 1, 0],
            [
                NativeInternalPointAvailability::Exact,
                NativeInternalPointAvailability::WordAperture,
            ],
        ),
        (
            [(1i128 << 65) + 1, -(1i128 << 66) - 7, 0, (1i128 << 64) + 3],
            [0, 0, 1, 2],
            [
                NativeInternalPointAvailability::WordAperture,
                NativeInternalPointAvailability::WordAperture,
            ],
        ),
        (
            [1, -2, 3, 5],
            [0, 0, 1, 1],
            [
                NativeInternalPointAvailability::NumericalEnclosure,
                NativeInternalPointAvailability::NumericalEnclosure,
            ],
        ),
    ] {
        let mut rest = mode.rest().unwrap();
        for (at, value) in wide.iter().enumerate() {
            rest.amplitude.intervals[2 * at] = (*value as i64, *value as i64);
            let high = (*value >> 64) as i64;
            rest.amplitude.intervals[2 * at + 1] = (high, high);
        }
        for (at, value) in point.into_iter().enumerate() {
            rest.amplitude.intervals[8 + at] = (value, value);
        }
        let mut bytes = Vec::new();
        rest.write(&mut bytes).unwrap();
        let restored = NativeSharedDriveMode::remount(
            &s,
            NativeSharedDriveModeRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap(),
        )
        .unwrap();
        let mut earlier = None;
        for steps in [0, u64::MAX, u64::MAX - 1] {
            let before = s.census();
            let returned = restored.unfold(steps).unwrap();
            assert_eq!(s.census().section_read_outs, before.section_read_outs);
            assert_eq!(s.census().ingress_octets, before.ingress_octets);
            let read = returned.inspect().unwrap();
            let sign = if steps & 1 == 0 { 1 } else { -1 };
            assert_eq!(
                read.current.center[0].real,
                Rat::new((sign * wide[0]).into(), wide[3].into())
            );
            assert_eq!(
                read.current.center[0].imaginary,
                Rat::new((sign * wide[1]).into(), wide[3].into())
            );
            assert_eq!(
                read.current.radius,
                Rat::new(wide[2].into(), wide[3].into())
            );
            assert_eq!(read.point_availability, expected[(steps & 1) as usize]);
            if read.point_availability != NativeInternalPointAvailability::Exact {
                let mut receiver = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
                assert!(receiver.advance_resident(returned.current(), None).is_err());
                assert_eq!(receiver.occurrences(), 0);
            }
            if steps == 0 {
                earlier = Some((returned, read));
            }
        }
        let (returned, read) = earlier.unwrap();
        assert_eq!(returned.inspect().unwrap(), read);
    }
}
