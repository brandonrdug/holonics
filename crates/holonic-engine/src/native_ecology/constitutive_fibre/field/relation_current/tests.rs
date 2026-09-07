use super::*;
use crate::embedding_fiber::ResidentReadout;

fn phase(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
fn seeds(nodes: usize) -> Vec<NativeJunctionSeed> {
    (0..nodes)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}
fn unique(returned: &ResidentConstitutiveReturn<'_>) -> Vec<Rat> {
    match returned.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => current,
        other => panic!("expected unique current, got {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; an actually formed field relation conducts a new native source"]
fn a_new_field_source_receives_learned_current_and_supplies_a_later_native_port() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found(&surface, seeds(1)).unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(2, 0)]))
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(4, 2)],
        ))
        .unwrap();
    // These are unlinked physical field operations, not newly supplied training pairs.
    field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(0, 0)]))
        .unwrap();
    let new = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(6, 0)]))
        .unwrap();
    let new_anchor = field.retain_source(&new.source).unwrap();
    let before_basis = field.inspect_relation().unwrap();
    let before_held = field.inspect_held().unwrap();
    let before_count = field.occurrence_count();
    let before = field.census();
    let response = field.read_constitutive_source(&new_anchor).unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    // The sole ingress is the one u32 predecessor address between the two native lanes.
    assert_eq!(
        field.census().ingress_octets - before.ingress_octets,
        std::mem::size_of::<u32>() as u64
    );
    assert_eq!(
        unique(&response),
        vec![Rat::from_integer(12.into()), Rat::from_integer(6.into())]
    );
    assert_eq!(field.occurrence_count(), before_count);
    assert_eq!(field.inspect_relation().unwrap(), before_basis);
    assert_eq!(field.inspect_held().unwrap(), before_held);

    let mut receiver = ResidentConstitutiveFibre::found(&surface, 2, 2).unwrap();
    receiver.advance(&[1, 0], Some(&[0, 1])).unwrap();
    receiver.advance(&[0, 1], Some(&[-1, 0])).unwrap();
    let before = receiver.census();
    let next = receiver.advance_resident(response.current(), None).unwrap();
    assert_eq!(
        receiver.census().section_read_outs,
        before.section_read_outs
    );
    assert_eq!(receiver.census().ingress_octets, before.ingress_octets);
    assert_eq!(
        unique(&next),
        vec![Rat::from_integer((-6).into()), Rat::from_integer(12.into())]
    );
    // The observer did not consume the independently held linear source capability.
    field
        .advance_resident(&mut NativeFieldOccurrence::through(
            new.source,
            vec![phase(1, 0)],
        ))
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; both historical branches cross a nonintegral phase frame"]
fn historical_query_is_frame_covariant_and_earlier_return_stays_immutable() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut material = seeds(1);
    material[0].initial_held = phase(1, 1);
    let mut field = NativeConstitutiveField::found(&surface, material).unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(2, 1)]))
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(4, 2)],
        ))
        .unwrap();
    let old = field.read_constitutive_source(&anchor).unwrap();
    let old_reading = old.inspect().unwrap();
    field
        .rechart(&[NativePhaseCurrent::new(3, 4, 5).unwrap()])
        .unwrap();
    let before = field.census();
    let now = field.read_constitutive_source(&anchor).unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    assert_eq!(unique(&old), unique(&now));
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(5, 2)],
        ))
        .unwrap();
    assert!(matches!(
        field
            .read_constitutive_source(&anchor)
            .unwrap()
            .inspect()
            .unwrap()
            .predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    assert_eq!(old.inspect().unwrap(), old_reading);
}

#[test]
#[ignore = "requires CUDA; a plural phase current has a fixed differential receiver"]
fn receiver_of_a_plural_fibre_does_not_require_a_selected_current() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found(&surface, seeds(2)).unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1, 0); 2]))
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    for arrival in [
        vec![phase(1, 0), phase(3, 0)],
        vec![phase(2, 2), phase(4, 2)],
    ] {
        field
            .advance_resident(&mut NativeFieldOccurrence::through_anchor(&anchor, arrival))
            .unwrap();
    }
    let fixed = field.read_constitutive_source(&anchor).unwrap();
    assert!(matches!(
        fixed.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    let face = fixed.read_differential_pairs(0, 1).unwrap();
    assert_eq!(face.field_source, Some(0));
    assert_eq!(face.relation_cut, 3);
    assert_eq!(face.status, NativeFieldReceiverStatus::Plural);
    assert_eq!(
        (
            face.positive,
            face.negative,
            face.unresolved,
            face.exact_zero
        ),
        (1, 0, 0, 0)
    );
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(1, 0), phase(4, 0)],
        ))
        .unwrap();
    let variable = field.read_constitutive_source(&anchor).unwrap();
    let face = variable.read_differential_pairs(0, 1).unwrap();
    assert_eq!(
        (
            face.positive,
            face.negative,
            face.unresolved,
            face.exact_zero
        ),
        (0, 0, 1, 0)
    );
    assert_eq!(fixed.read_differential_pairs(0, 1).unwrap().positive, 1);
}

#[test]
#[ignore = "requires CUDA; foreign sources refuse before native query"]
fn foreign_source_and_unobserved_domain_remain_distinct() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut left = NativeConstitutiveField::found(&surface, seeds(2)).unwrap();
    let mut right = NativeConstitutiveField::found(&surface, seeds(2)).unwrap();
    let first = left
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1, 0); 2]))
        .unwrap();
    let anchor = left.retain_source(&first.source).unwrap();
    let before = right.census();
    assert!(matches!(
        right.read_constitutive_source(&anchor),
        Err(ConstitutiveFibreError::ForeignOccurrence)
    ));
    assert_eq!(right.census(), before);
    let open = left.read_constitutive_source(&anchor).unwrap();
    assert!(matches!(
        open.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    let face = open.read_differential_pairs(0, 1).unwrap();
    assert_eq!(
        (
            face.positive,
            face.negative,
            face.unresolved,
            face.exact_zero
        ),
        (0, 0, 1, 0)
    );
}

#[test]
#[ignore = "requires CUDA; an archived historical source queries the same relation after rest"]
fn archived_source_and_remount_preserve_the_resident_receiver() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let path = std::env::temp_dir().join(format!(
        "holonics-relation-source-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let mut field = NativeConstitutiveField::found(&surface, seeds(1)).unwrap();
    field.enable_history_archive(&path).unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(2, 1)]))
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(4, 3)],
        ))
        .unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(0, 0)]))
        .unwrap();
    field
        .archive_history_before(field.occurrence_count())
        .unwrap();
    let before = field.history_placement();
    let returned = field.read_constitutive_source(&anchor).unwrap();
    assert_eq!(
        field.history_placement().restored_sources,
        before.restored_sources + 1
    );
    let expected = returned.inspect().unwrap();
    let rest = field.rest(&[], &[Some(&anchor)]).unwrap();
    let count = field.occurrence_count();
    drop(field);
    let (mut remounted, _, anchors) = NativeConstitutiveField::remount(&surface, rest).unwrap();
    let actual = remounted
        .read_constitutive_source(anchors[0].as_ref().unwrap())
        .unwrap();
    assert_eq!(actual.inspect().unwrap(), expected);
    assert_eq!(remounted.occurrence_count(), count);
    drop(remounted);
    std::fs::remove_file(path).unwrap();
}
