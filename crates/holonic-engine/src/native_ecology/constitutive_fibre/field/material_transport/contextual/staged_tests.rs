use super::*;
use crate::embedding_fiber::ResidentReadout;

fn current(at: usize) -> NativePhaseCurrent {
    let directions = [(1, 0), (0, 1), (-1, 0), (0, -1)];
    let (r, i) = directions[at % directions.len()];
    NativePhaseCurrent::new(r, i, 3).unwrap()
}

fn run<'c>(
    surface: &'c ResidentSurface<'c>,
    fused: bool,
    nodes: usize,
    source: NativeMaterialTransportSource,
    target: NativeMaterialTarget,
    count: usize,
    deform: bool,
) -> NativeFieldRest {
    let seed = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        nodes
    ];
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(surface, seed, ResidentGrain(72))
            .unwrap();
    field.fused_contextual = fused;
    field
        .enable_material_transport_chart(source, target)
        .unwrap();
    let mut last = None;
    let mut anchor = None;
    for at in 0..count {
        if at == count / 2 {
            field
                .rechart(&vec![NativePhaseCurrent::new(0, 1, 1).unwrap(); nodes])
                .unwrap();
        }
        // The legacy implicit-current profiles use their established unit/integral-contact control;
        // operative profiles retain the broader non-dyadic control.
        let incoming = (0..nodes)
            .map(|node| {
                let value = current(at + node);
                if source.is_operative() {
                    value
                } else {
                    let [r, i, _] = value.words();
                    NativePhaseCurrent::new(r, i, 1).unwrap()
                }
            })
            .collect();
        let mut occurrence = if at == count / 2 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), incoming)
        } else if let Some(source) = last.take() {
            NativeFieldOccurrence::through(source, incoming)
        } else {
            NativeFieldOccurrence::entering(incoming)
        };
        let before = field.census();
        let step = field.advance_resident(&mut occurrence).unwrap_or_else(|e| {
            panic!("fused={fused} source={source:?} nodes={nodes} at={at}: {e}")
        });
        assert_eq!(field.census().section_read_outs, before.section_read_outs);
        if at == 0 {
            anchor = Some(field.retain_source(&step.source).unwrap());
        }
        if deform && at == count / 2 && source.is_operative() {
            field
                .respond_to_material_observation(
                    at,
                    NativeMaterialResponseChart::ComplexCurrent,
                    NativeContactRealization::DyadicDeposit,
                    |_, _| (),
                )
                .unwrap();
        }
        last = Some(step.source);
    }
    field.rest(&[last.as_ref()], &[anchor.as_ref()]).unwrap()
}

#[test]
#[ignore = "requires CUDA; staged and fused kernels retain the complete field across source/target profiles"]
fn staged_contextual_matches_fused_complete_successors() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    for source in [
        NativeMaterialTransportSource::Contextual,
        NativeMaterialTransportSource::BilinearContextual,
        NativeMaterialTransportSource::OperativeContextual,
        NativeMaterialTransportSource::OperativeBoundary,
    ] {
        assert_eq!(
            run(
                &surface,
                true,
                2,
                source,
                NativeMaterialTarget::DirectCurrent,
                6,
                true
            ),
            run(
                &surface,
                false,
                2,
                source,
                NativeMaterialTarget::DirectCurrent,
                6,
                true
            )
        );
        if source.is_operative() {
            assert_eq!(
                run(
                    &surface,
                    false,
                    6,
                    source,
                    NativeMaterialTarget::TensorProduct { factor_width: 2 },
                    6,
                    true
                ),
                run(
                    &surface,
                    true,
                    6,
                    source,
                    NativeMaterialTarget::TensorProduct { factor_width: 2 },
                    6,
                    true
                )
            );
        }
    }
}

#[test]
#[ignore = "requires CUDA; actual source rows cross a device block boundary without changing reduction order"]
fn staged_contextual_crosses_the_device_block_boundary() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let count = surface.derived_launch().0 as usize + 2;
    eprintln!("comparing {count} actual occurrences across the derived block boundary");
    assert_eq!(
        run(
            &surface,
            false,
            1,
            NativeMaterialTransportSource::OperativeContextual,
            NativeMaterialTarget::DirectCurrent,
            count,
            false
        ),
        run(
            &surface,
            true,
            1,
            NativeMaterialTransportSource::OperativeContextual,
            NativeMaterialTarget::DirectCurrent,
            count,
            false
        )
    );
}

#[test]
#[ignore = "requires CUDA; a weight-stage refusal cannot commit a prepared relation row or held current"]
fn staged_contextual_weight_refusal_preserves_predecessor() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
        ResidentGrain(72),
    )
    .unwrap();
    field
        .enable_material_transport_source(NativeMaterialTransportSource::OperativeContextual)
        .unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![current(0)]))
        .unwrap();
    let second = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![current(1)],
        ))
        .unwrap();
    let before = field.rest(&[Some(&second.source)], &[]).unwrap();
    let original = Rc::clone(
        field.history[1]
            .resident()
            .unwrap()
            .transport
            .as_ref()
            .unwrap(),
    );
    let mut bad = surface.detach_section(&original, 64).unwrap();
    // Zero the stored source norm used by the kernel denominator, leaving the source/profile
    // prologue intact. This failure belongs to the later independent weight stage.
    let norm = offsets(1)[2] + 16 + 2;
    bad.intervals[norm..norm + 5].fill((0, 0));
    field.history[1].resident.as_mut().unwrap().transport =
        Some(Rc::new(surface.mount_section_rest(&bad).unwrap()));
    let mut event = NativeFieldOccurrence::through(second.source, vec![current(2)]);
    assert!(field.advance_resident(&mut event).is_err());
    field.history[1].resident.as_mut().unwrap().transport = Some(original);
    assert_eq!(field.rest(&[event.source_ref()], &[]).unwrap(), before);
    field.advance_resident(&mut event).unwrap();
    assert_eq!(field.occurrence_count(), 3);
}
