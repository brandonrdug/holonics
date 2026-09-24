use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn material(nodes: usize) -> Vec<NativeJunctionSeed> {
    (0..nodes)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}
fn phase(a: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(a, 0, 1).unwrap()
}

/// Parity law (material transport): the device forward ball contains the exact host-reconstructed
/// forward current, and returned − chronological = contemporary difference.
#[test]
#[ignore = "requires CUDA; native contextual coefficients and old/current returned differences"]
fn transport_uses_the_retained_context_and_reconstructs_its_exact_coefficients() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    field.enable_material_transport().unwrap();
    let before = field.census();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    let anchor = field.retain_source(&first.source).unwrap();
    let initial = field.inspect_material_transport(0).unwrap().unwrap();
    assert!(initial
        .forward
        .center
        .iter()
        .all(ExactComplexWaveCurrent::is_zero));
    assert_eq!(initial.forward.radius, Rat::zero());
    assert!(initial.returned_difference.is_none());
    let second = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(1)],
        ))
        .unwrap();
    let one = field.inspect_exact_material_transport(1).unwrap().unwrap();
    assert_eq!(
        one.coefficients[0][1],
        ExactComplexWaveCurrent::new(Rat::new(1.into(), 2.into()), Rat::zero())
    );
    field
        .advance_resident(&mut NativeFieldOccurrence::through(
            second.source,
            vec![phase(2)],
        ))
        .unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(3)],
        ))
        .unwrap();
    let reading = field.inspect_material_transport(3).unwrap().unwrap();
    let returned = &reading.returned_difference.as_ref().unwrap().center;
    let chronology = &reading.chronological_current.as_ref().unwrap().center;
    assert_eq!(
        subtract(returned, chronology),
        reading.contemporary_difference.as_ref().unwrap().center
    );
    assert!(chronology.iter().any(|x| !x.is_zero()));
    let exact = field.inspect_exact_material_transport(3).unwrap().unwrap();
    assert!(reading.forward.contains(&exact.forward));
    let residual = field
        .inspect_material_transport_residual(3)
        .unwrap()
        .unwrap();
    assert_eq!(residual.parameter_update.len(), 1);
    assert_eq!(residual.parameter_update[0].len(), 3);
}
