use super::*;
use crate::embedding_fiber::{AlignedMaterial, MountedReadout, ResidentReadout};

fn points<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                64,
                values.iter().map(|v| (*v, *v)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
}

fn current<'a, 'c>(section: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(section).unwrap()
}

fn physical_return<'c>(
    surface: &'c ResidentSurface<'c>,
    source: &ResidentSection<'c>,
    map: &MountedReadout<'c>,
) -> ResidentSection<'c> {
    let result = surface
        .fresh_section(1, map.rows(), ResidentGrain(0))
        .unwrap();
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface
            .record_contract(&lane, source, map, &result)
            .unwrap();
    }
    passage.close(0, &result, 64).unwrap();
    assert!(
        passage
            .finish()
            .unwrap()
            .launch()
            .unwrap()
            .obstruction
            .is_empty()
    );
    result
}

fn values(result: &ResidentConstitutiveReturn<'_>) -> Vec<Rat> {
    match result.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => current,
        other => panic!("expected unique current, got {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; observed native phase action conducts from partial knowledge"]
fn limited_native_observations_conduct_a_new_superposition_without_host_readout() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    // Exterior apparatus exposes (i/2)*z and an independent third source channel. The learner
    // never sees this operator, and the two observed returns leave its third channel unknown.
    let apparatus = readout
        .mount(
            &AlignedMaterial {
                entries: vec![0, -1, 9, 1, 0, 7],
                exponent: -1,
                entry_octaves: 4,
                negatives: 1,
            },
            3,
        )
        .unwrap();
    let mut relation = ResidentConstitutiveFibre::found(&surface, 3, 2).unwrap();
    let inputs = [[2, 0, 0], [0, 2, 0]].map(|v| points(&surface, &v));
    let probe = points(&surface, &[3, 4, 0]);
    let missing = points(&surface, &[0, 0, 1]);
    let before = surface.census();
    for source in &inputs {
        let returned = physical_return(&surface, source, &apparatus);
        relation
            .advance_resident(current(source), Some(current(&returned)))
            .unwrap();
    }
    let learned = relation.advance_resident(current(&probe), None).unwrap();
    let open = relation.advance_resident(current(&missing), None).unwrap();
    let after = surface.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.ingress_octets, before.ingress_octets);
    assert_eq!(
        values(&learned),
        vec![Rat::from_integer((-2).into()), Rat::new(3.into(), 2.into())]
    );
    assert!(matches!(
        open.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    assert_eq!(learned.inspect().unwrap().successor_rank, 2);
}

#[test]
#[ignore = "requires CUDA; rational emitted current re-enters the same learned relation"]
fn rational_phase_returns_continue_without_remount_or_rounding() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let apparatus = readout
        .mount(
            &AlignedMaterial {
                entries: vec![0, -1, 1, 0],
                exponent: -1,
                entry_octaves: 1,
                negatives: 1,
            },
            2,
        )
        .unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 2, 2).unwrap();
    for input in [[2, 0], [0, 2]] {
        let source = points(&surface, &input);
        let observed = physical_return(&surface, &source, &apparatus);
        body.advance_resident(current(&source), Some(current(&observed)))
            .unwrap();
    }
    let source = points(&surface, &[1, 0]);
    let before = surface.census();
    let first = body.advance_resident(current(&source), None).unwrap();
    let second = body.advance_resident(first.current(), None).unwrap();
    let third = body.advance_resident(second.current(), None).unwrap();
    assert_eq!(surface.census().section_read_outs, before.section_read_outs);
    assert_eq!(surface.census().ingress_octets, before.ingress_octets);
    assert_eq!(
        values(&first),
        vec![Rat::from_integer(0.into()), Rat::new(1.into(), 2.into())]
    );
    assert_eq!(
        values(&second),
        vec![Rat::new((-1).into(), 4.into()), Rat::from_integer(0.into())]
    );
    assert_eq!(
        values(&third),
        vec![Rat::from_integer(0.into()), Rat::new((-1).into(), 8.into())]
    );
    // The rational return itself may later be an actual observation at another local port.
    let mut later = ResidentConstitutiveFibre::found(&surface, 2, 2).unwrap();
    later
        .advance_resident(first.current(), Some(second.current()))
        .unwrap();
    assert_eq!(
        values(&later.advance_resident(first.current(), None).unwrap()),
        values(&second)
    );
}

#[test]
#[ignore = "requires CUDA; immutable plural face survives later development"]
fn earlier_preimage_fibre_is_not_rewritten_and_cannot_be_used_as_a_point() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 1, 2).unwrap();
    body.advance(&[1], Some(&[2, 3])).unwrap();
    body.advance(&[1], Some(&[3, 3])).unwrap();
    let source = points(&surface, &[1]);
    let old = body.advance_resident(current(&source), None).unwrap();
    let old_reading = old.inspect().unwrap();
    body.advance(&[1], Some(&[2, 4])).unwrap();
    assert_eq!(old.inspect().unwrap(), old_reading);
    match old_reading.predecessor_reading {
        ConstitutiveReading::Plural { directions, .. } => assert_eq!(directions.len(), 1),
        other => panic!("expected plural face: {other:?}"),
    }
    let mut consumer = ResidentConstitutiveFibre::found(&surface, 2, 1).unwrap();
    let before = consumer.inspect_relation().unwrap();
    let receive = points(&surface, &[9]);
    assert!(
        consumer
            .advance_resident(old.current(), Some(current(&receive)))
            .is_err()
    );
    assert_eq!(consumer.occurrences(), 0);
    assert_eq!(consumer.inspect_relation().unwrap(), before);
    consumer.advance(&[1, 0], Some(&[1])).unwrap();
}

#[test]
#[ignore = "requires CUDA; resident refusal leaves the single continuing relation unchanged"]
fn overflow_and_nonpoint_operands_refuse_before_deposit() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&surface, 2, 1).unwrap();
    body.advance(&[i64::MAX, 1], Some(&[i64::MAX])).unwrap();
    let before = body.inspect_relation().unwrap();
    let source = points(&surface, &[1, i64::MAX]);
    let received = points(&surface, &[0]);
    assert!(
        body.advance_resident(current(&source), Some(current(&received)))
            .is_err()
    );
    assert_eq!(body.inspect_relation().unwrap(), before);
    assert_eq!(body.occurrences(), 1);
    let interval = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), 64, vec![(0, 1), (0, 0)]).unwrap(),
        )
        .unwrap();
    assert!(body.advance_resident(current(&interval), None).is_err());
    assert_eq!(body.inspect_relation().unwrap(), before);
    let zero = points(&surface, &[0, 0]);
    assert_eq!(
        values(&body.advance_resident(current(&zero), None).unwrap()),
        vec![Rat::from_integer(0.into())]
    );
}

#[test]
#[ignore = "requires CUDA; borrowed current has an actual resident surface"]
fn a_different_surface_does_not_supply_this_relations_current() {
    let readout = ResidentReadout::new().unwrap();
    let left = ResidentSurface::on(&readout).unwrap();
    let right = ResidentSurface::on(&readout).unwrap();
    let source = points(&left, &[1]);
    let mut body = ResidentConstitutiveFibre::found(&right, 1, 1).unwrap();
    assert!(body.advance_resident(current(&source), None).is_err());
    assert_eq!(body.occurrences(), 0);
}
