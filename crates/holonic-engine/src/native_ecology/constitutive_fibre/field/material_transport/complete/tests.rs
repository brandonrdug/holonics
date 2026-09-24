use super::*;
use crate::embedding_fiber::ResidentReadout;

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

/// Parity law (complete material transport): `inspect_exact_complete_material_transport` rebuilds
/// the exact source-qualified operator on the host and refuses unless every device ball contains it.
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
