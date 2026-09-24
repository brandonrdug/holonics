use super::*;
use crate::embedding_fiber::ResidentReadout;

/// Differential-receiver parity: the device pair reading is resolved exactly when the host
/// criterion `margin² > 2·radius²` holds on the cold enclosure, with the host sign; reading
/// leaves the field able to continue.
#[test]
#[ignore = "requires CUDA; terminal current observation leaves the native owner and source available"]
fn differential_receiver_certifies_the_exact_host_margin_and_preserves_continuation() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let material = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        2
    ];
    let mut body = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material,
        ResidentGrain(72),
    )
    .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
    let zero = body.read_differential_pairs(0, 4, 1).unwrap().unwrap();
    assert_eq!((zero.unresolved, zero.exact_zero), (1, 1));
    // Invalid receiver declarations refuse before opening a capture and leave future use lawful.
    assert!(matches!(
        body.read_differential_pairs(0, 6, 1),
        Err(ConstitutiveFibreError::Shape)
    ));
    let next = body
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![NativePhaseCurrent::zero(), NativePhaseCurrent::unit()],
        ))
        .unwrap();
    let before = body.inspect_junction(1).unwrap();
    let reading = body.read_differential_pairs(1, 4, 1).unwrap().unwrap();
    let cold = body
        .inspect_junction_enclosure(1)
        .unwrap()
        .unwrap()
        .outgoing;
    let margin = &cold.center[5].real - &cold.center[4].real;
    let certain = &margin * &margin > Rat::from_integer(2.into()) * &cold.radius * &cold.radius;
    assert_eq!(reading.unresolved == 0, certain);
    if certain {
        assert_eq!(reading.positive == 1, margin > Rat::from_integer(0.into()));
    }
    assert_eq!(body.occurrence_count(), 2);
    assert_eq!(body.inspect_junction(1).unwrap(), before);
    body.advance_resident(&mut NativeFieldOccurrence::through(
        next.source,
        vec![NativePhaseCurrent::unit(), NativePhaseCurrent::zero()],
    ))
    .unwrap();
    assert_eq!(body.occurrence_count(), 3);
}
