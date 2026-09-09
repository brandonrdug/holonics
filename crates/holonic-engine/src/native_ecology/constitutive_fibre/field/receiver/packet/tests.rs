use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::SeriesAperture;
fn input(word: usize, imaginary: bool) -> Vec<NativePhaseCurrent> {
    (0..6)
        .map(|i| {
            if (word >> (i / 2)) & 1 == i % 2 {
                if imaginary && i / 2 == 0 {
                    NativePhaseCurrent::new(0, 1, 1).unwrap()
                } else {
                    NativePhaseCurrent::unit()
                }
            } else {
                NativePhaseCurrent::zero()
            }
        })
        .collect()
}
fn make<'c>(surface: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let seeds = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        6
    ];
    let mut f =
        NativeConstitutiveField::found_with_enclosed_junction(surface, seeds, ResidentGrain(72))
            .unwrap();
    f.enable_material_transport_chart(
        NativeMaterialTransportSource::OperativeBoundary,
        NativeMaterialTarget::TensorProduct { factor_width: 2 },
    )
    .unwrap();
    f
}
fn populate(f: &mut NativeConstitutiveField<'_>) -> NativeFieldEmission {
    let a = f
        .advance_resident(&mut NativeFieldOccurrence::entering(input(3, false)))
        .unwrap();
    f.advance_resident(&mut NativeFieldOccurrence::through(
        a.source,
        input(5, true),
    ))
    .unwrap()
    .source
}
#[test]
#[ignore = "requires CUDA; applied material keeps lineage, rejects wrong faces and does not refit its own projection"]
fn material_actuation_keeps_its_source_and_advances_without_a_new_observation() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut f = make(&s);
    let source = populate(&mut f);
    let actuation = f
        .read_material_actuation(&source, NativePacketQuadrature::Imaginary)
        .unwrap();
    assert_eq!(actuation.reading().selected, Some(5));
    let before = f.rest(&[], &[]).unwrap();
    let geometry = f.stage_operative_contacts().unwrap().inspect().unwrap();
    let material = f.inspect_contextual_material_transport(1).unwrap().unwrap();
    let mut event = NativeFieldOccurrence::actuating(source, input(2, true), actuation);
    assert!(f.advance_resident(&mut event).is_err());
    assert!(event.source_ref().is_some());
    assert_eq!(f.rest(&[], &[]).unwrap(), before);
    event.incoming = input(5, true);
    let next = f.advance_resident(&mut event).unwrap();
    assert_eq!(next.lineage.received_from, Some(1));
    assert_eq!(next.lineage.observed_source(), None);
    assert_eq!(
        next.lineage.source_contact,
        Some(NativeFieldSourceContact::MaterialActuation {
            quadrature: NativePacketQuadrature::Imaginary,
            coordinate: 5
        })
    );
    let after = f.stage_operative_contacts().unwrap().inspect().unwrap();
    assert_eq!(geometry.births, after.births);
    assert_eq!(geometry.contacts, after.contacts);
    let now = f.inspect_contextual_material_transport(2).unwrap().unwrap();
    assert_eq!(material.coefficient_error, now.coefficient_error);
    assert_eq!(material.coefficient_norm_upper, now.coefficient_norm_upper);
    assert!(
        now.ordinary_factor
            .iter()
            .chain(&now.contextual_factor)
            .all(|x| *x == ExactComplexWaveCurrent::zero())
    );
    assert!(
        f.normalized_material_return(2, 8, SeriesAperture(32))
            .unwrap()
            .is_none()
    );
    assert!(f.pull_back_material_current(2).unwrap().is_none());
    let saved = f.rest(&[Some(&next.source)], &[]).unwrap();
    let mut bytes = vec![];
    saved.write(&mut bytes).unwrap();
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let next = f
        .advance_resident(&mut NativeFieldOccurrence::through(
            next.source,
            input(6, false),
        ))
        .unwrap();
    assert_eq!(next.lineage.observed_source(), Some(2));
    assert_eq!(
        f.stage_operative_contacts()
            .unwrap()
            .inspect()
            .unwrap()
            .births
            .len(),
        geometry.births.len() + 1
    );
    let expected = f.rest(&[Some(&next.source)], &[]).unwrap();
    drop(f);
    let (mut f, mut sources, _) = NativeConstitutiveField::remount(&s, saved).unwrap();
    let next = f
        .advance_resident(&mut NativeFieldOccurrence::through(
            sources[0].take().unwrap(),
            input(6, false),
        ))
        .unwrap();
    assert_eq!(f.rest(&[Some(&next.source)], &[]).unwrap(), expected);
}
#[test]
#[ignore = "requires CUDA; actuation witness cannot be rebound to a foreign source"]
fn material_actuation_rejects_a_foreign_witness_without_consuming_source() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut a = make(&s);
    let source = populate(&mut a);
    let witness = a
        .read_material_actuation(&source, NativePacketQuadrature::Imaginary)
        .unwrap();
    let mut b = make(&s);
    let other = populate(&mut b);
    let before = b.rest(&[], &[]).unwrap();
    let mut event = NativeFieldOccurrence::actuating(other, input(5, true), witness);
    assert!(matches!(
        b.advance_resident(&mut event),
        Err(ConstitutiveFibreError::ForeignOccurrence)
    ));
    assert!(event.source_ref().is_some());
    assert_eq!(b.rest(&[], &[]).unwrap(), before);
}
