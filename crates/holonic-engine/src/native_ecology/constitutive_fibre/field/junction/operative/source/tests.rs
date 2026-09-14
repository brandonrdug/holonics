use super::super::tests::{populate, seed};
use super::*;
use crate::embedding_fiber::ResidentReadout;

#[test]
#[ignore = "requires CUDA; resident field source joins outgoing and operative internal carriers"]
fn source_packs_boundary_and_internal_b_without_host_readout() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    populate(&mut field);
    let before = field.census().section_read_outs;
    let source = field.read_current_source().unwrap();
    assert_eq!(field.census().section_read_outs, before);
    assert_eq!(source.field_cut(), field.occurrence_count());
    assert_eq!(source.occurrence(), Some(field.occurrence_count() - 1));
    assert_eq!(source.boundary_components(), 6);
    assert!(source.internal_components() >= 4);
    assert_eq!(
        source.enclosure().components(),
        6 + source.internal_components()
    );
    assert!(source.same_owner(&source));
    let births = source.births().to_vec();
    let actual = source.enclosure().inspect().unwrap();
    let boundary = field
        .inspect_junction_enclosure(3)
        .unwrap()
        .unwrap()
        .outgoing;
    let interior = field
        .stage_operative_contacts()
        .unwrap()
        .inspect()
        .unwrap()
        .internal;
    let expected = boundary
        .center
        .into_iter()
        .chain(interior.center)
        .collect::<Vec<_>>();
    assert_eq!(actual.center, expected);
    assert_eq!(actual.radius, boundary.radius + interior.radius);
    assert!(
        actual.center[3..]
            .iter()
            .any(|v| *v != ExactComplexWaveCurrent::zero())
    );
    let mut later =
        NativeFieldOccurrence::entering(vec![NativePhaseCurrent::new(2, 0, 1).unwrap()]);
    field.advance_resident(&mut later).unwrap();
    assert_eq!(source.field_cut(), 4);
    assert_eq!(source.internal_components(), 2 * births.len());
    assert_eq!(source.births(), births);
    assert_eq!(source.enclosure().inspect().unwrap(), actual);
}

#[test]
#[ignore = "requires CUDA; an aggregate-dark boundary still exposes its opposite internal currents"]
fn source_retains_dark_internal_pair() {
    use crate::native_ecology::constitutive_fibre::field::internal_current::tests::dark;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let (mut field, _) = dark(&s, true, NativePhaseCurrent::new(0, 1, 1).unwrap());
    let exact = field.inspect_internal_currents().unwrap().unwrap();
    let source = field.read_current_source().unwrap();
    let read = source.enclosure().inspect().unwrap();
    let boundary = field
        .inspect_junction_enclosure(field.occurrence_count() - 1)
        .unwrap()
        .unwrap();
    let zero = ExactComplexWaveCurrent::zero();
    assert!(boundary.outgoing.contains(&vec![zero.clone(); 3]));
    assert!(boundary.held_current.contains(&vec![zero.clone(); 3]));
    assert!(exact.iter().any(|v| v.current != zero));
    let mut complete = vec![zero; 3];
    complete.extend(exact.into_iter().map(|v| v.current));
    assert!(read.contains(&complete));
}
