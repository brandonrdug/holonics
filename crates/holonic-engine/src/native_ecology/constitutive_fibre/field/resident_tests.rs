use super::*;
use crate::embedding_fiber::ResidentReadout;

fn phase(real: i64, imaginary: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, 1).unwrap()
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

#[test]
#[ignore = "requires CUDA; delayed sources, rechart, full enclosure and legacy status equality"]
fn resident_and_observed_runs_keep_the_same_native_successor() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut resident = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seeds(2),
        ResidentGrain(72),
    )
    .unwrap();
    let mut observed = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seeds(2),
        ResidentGrain(72),
    )
    .unwrap();
    let inputs = [
        vec![phase(1, 0), phase(0, 1)],
        vec![phase(2, 1), phase(-1, 2)],
        vec![phase(1, -1), phase(2, 0)],
        vec![phase(0, 1), phase(1, 1)],
        vec![phase(-1, 0), phase(2, -1)],
    ];
    let links = [None, None, Some(0), Some(1), Some(2)];
    let mut resident_sources: Vec<Option<NativeFieldEmission>> = Vec::new();
    let mut observed_sources: Vec<Option<NativeFieldEmission>> = Vec::new();
    let mut statuses = Vec::new();
    for (at, incoming) in inputs.into_iter().enumerate() {
        if at == 2 {
            let turns = vec![phase(0, 1), phase(0, -1)];
            resident.rechart(&turns).unwrap();
            observed.rechart(&turns).unwrap();
        }
        let mut r = match links[at] {
            Some(source) => NativeFieldOccurrence::through(
                resident_sources[source].take().unwrap(),
                incoming.clone(),
            ),
            None => NativeFieldOccurrence::entering(incoming.clone()),
        };
        let mut o = match links[at] {
            Some(source) => {
                NativeFieldOccurrence::through(observed_sources[source].take().unwrap(), incoming)
            }
            None => NativeFieldOccurrence::entering(incoming),
        };
        let before = resident.census();
        let next = resident.advance_resident(&mut r).unwrap();
        let after = resident.census();
        assert_eq!(after.section_read_outs, before.section_read_outs);
        assert_eq!(after.egress_section_octets, before.egress_section_octets);
        assert_eq!(after.deed_launches, before.deed_launches + 1);
        let step = observed.advance_status(&mut o).unwrap();
        assert_eq!(next.lineage, step.lineage);
        assert_eq!(next.frame.ordinal(), step.frame.ordinal());
        assert_eq!(next.frame.root_to_local(), step.frame.root_to_local());
        assert_eq!(step.outgoing.len(), 2);
        assert_eq!(step.held_successor.len(), 2);
        assert!(step.junction.as_ref().unwrap().enclosed().is_some());
        statuses.push(NativeFieldOccurrenceStatus {
            receiver: step.receiver,
            former_receiver: step.received_difference.as_ref().map(|r| r.former_receiver),
            formed_pivot: step.formed_pivot,
            successor_rank: step.successor_rank,
        });
        resident_sources.push(Some(next.source));
        observed_sources.push(Some(step.source));
    }
    assert_eq!(resident.lineage(2).unwrap().received_from, Some(0));
    assert_eq!(resident.lineage(2).unwrap().frame, 1);
    assert_eq!(resident.source_frame(0).unwrap().ordinal(), 0);
    assert_eq!(
        resident.inspect_relation().unwrap(),
        observed.inspect_relation().unwrap()
    );
    assert_eq!(
        resident.inspect_held().unwrap(),
        observed.inspect_held().unwrap()
    );
    assert_eq!(
        resident.inspect_junction_covariance().unwrap(),
        observed.inspect_junction_covariance().unwrap()
    );
    for at in 0..resident.occurrence_count() {
        assert_eq!(
            resident.inspect_source(at).unwrap(),
            observed.inspect_source(at).unwrap()
        );
        assert_eq!(
            resident.inspect_junction(at).unwrap(),
            observed.inspect_junction(at).unwrap()
        );
        assert_eq!(
            resident.inspect_occurrence_status(at).unwrap(),
            statuses[at]
        );
    }
    assert_eq!(
        resident.inspect_internal_current_enclosures().unwrap(),
        observed.inspect_internal_current_enclosures().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; actual covariance carrier refusal retains the old owner and source"]
fn resident_refusal_retains_the_source_and_can_receive_it_after_repair() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seeds(1),
        ResidentGrain(72),
    )
    .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1, 0)]))
        .unwrap();
    let held = body.inspect_held().unwrap();
    let relation = body.inspect_relation().unwrap();
    let covariance = body.inspect_junction_covariance().unwrap();
    let junction = body.inspect_junction(0).unwrap();
    let mut refused = NativeFieldOccurrence::through(first.source, vec![phase(i64::MAX, 0)]);
    assert!(matches!(
        body.advance_resident(&mut refused),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.occurrence_count(), 1);
    assert!(body.pending_lineage().is_none());
    assert_eq!(body.inspect_held().unwrap(), held);
    assert_eq!(body.inspect_relation().unwrap(), relation);
    assert_eq!(body.inspect_junction_covariance().unwrap(), covariance);
    assert_eq!(body.inspect_junction(0).unwrap(), junction);
    let source = refused
        .take_source()
        .expect("refusal retains the actual source");
    let returned = body
        .advance_resident(&mut NativeFieldOccurrence::through(
            source,
            vec![phase(1, 0)],
        ))
        .unwrap();
    assert_eq!(returned.lineage.received_from, Some(0));
    assert_eq!(body.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; foreign rejection preserves a recoverable source"]
fn resident_foreign_handle_can_still_return_to_its_actual_owner() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut left = NativeConstitutiveField::found(&surface, seeds(1)).unwrap();
    let mut right = NativeConstitutiveField::found(&surface, seeds(1)).unwrap();
    let source = left
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1, 0)]))
        .unwrap()
        .source;
    let mut wrong = NativeFieldOccurrence::through(source, vec![phase(1, 0)]);
    assert!(matches!(
        right.advance_resident(&mut wrong),
        Err(ConstitutiveFibreError::ForeignOccurrence)
    ));
    assert_eq!(right.occurrence_count(), 0);
    let source = wrong.take_source().unwrap();
    left.advance_resident(&mut NativeFieldOccurrence::through(
        source,
        vec![phase(1, 0)],
    ))
    .unwrap();
    assert_eq!(left.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; an observer error after enactment preserves pending uncertainty"]
fn observer_failure_does_not_report_a_native_rollback() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveField::found(&surface, seeds(1)).unwrap();
    let mut occurrence = NativeFieldOccurrence::entering(vec![phase(1, 0)]);
    let failed = body.advance_with(&mut occurrence, |_, _, _| {
        Err::<(), _>(ConstitutiveFibreError::Uncertain)
    });
    assert!(matches!(failed, Err(ConstitutiveFibreError::Uncertain)));
    assert_eq!(body.occurrence_count(), 0);
    assert_eq!(body.pending_lineage().unwrap().occurrence, 0);
    assert!(matches!(
        body.advance_resident(&mut occurrence),
        Err(ConstitutiveFibreError::Uncertain)
    ));
}
