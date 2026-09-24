use super::*;
use crate::embedding_fiber::ResidentReadout;

fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        nodes
    ]
}
fn dot(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> ExactComplexWaveCurrent {
    a.iter()
        .zip(b)
        .fold(ExactComplexWaveCurrent::zero(), |sum, (a, b)| {
            sum.add(&a.conjugate().multiply(b))
        })
}

/// Host/device parity (current-history-source kernel): the device norm square and self-pairing
/// equal the host dot product of the complete current, with birth squares wider than 128 bits.
#[test]
#[ignore = "requires CUDA; exact birth squares exceed 128 bits in the ordinary 72-bit current chart"]
fn birth_square_and_norm_keep_their_wider_numerators() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    let mut receiver = NativeCurrentHistorySourceReceiver::on_empty(&body).unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(1024, 1, 1).unwrap(),
        ]))
        .unwrap();
    receiver.receive_completed(&body).unwrap();
    body.advance_resident(&mut NativeFieldOccurrence::through(
        first.source,
        vec![NativePhaseCurrent::new(1, -1024, 1).unwrap()],
    ))
    .unwrap();
    let source = receiver.receive_completed(&body).unwrap();
    let state = surface.read_out(&receiver.state).unwrap();
    assert!(integer(&state[12..17]).unwrap().bits() > 128);
    let reading = receiver.inspect(&source).unwrap();
    let mut full = body
        .inspect_junction_enclosure(1)
        .unwrap()
        .unwrap()
        .outgoing
        .center;
    full.extend(
        body.inspect_internal_current_enclosures()
            .unwrap()
            .unwrap()
            .into_iter()
            .map(|i| i.current.center[0].clone()),
    );
    assert_eq!(reading.numerical_norm_square, dot(&full, &full).real);
    assert_eq!(
        receiver.pairing(&source, &source).unwrap().center[0].real,
        reading.numerical_norm_square
    );
}
