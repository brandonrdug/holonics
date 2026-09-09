use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::SeriesAperture;

fn phase(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
fn make<'c>(s: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let seed = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        2
    ];
    let mut f =
        NativeConstitutiveField::found_with_enclosed_junction(s, seed, ResidentGrain(72)).unwrap();
    f.enable_material_transport_source(NativeMaterialTransportSource::OperativeContextual)
        .unwrap();
    f
}
fn populate(f: &mut NativeConstitutiveField<'_>) -> NativeFieldEmission {
    let mut last = None;
    let mut anchor = None;
    for (at, v) in [
        [(1, 1), (0, 1)],
        [(0, 1), (1, 0)],
        [(1, 0), (0, -1)],
        [(0, 0), (1, 1)],
        [(1, 0), (0, 0)],
    ]
    .into_iter()
    .enumerate()
    {
        let incoming = v.into_iter().map(|(r, i)| phase(r, i)).collect();
        let mut event = if at == 2 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), incoming)
        } else if let Some(s) = last.take() {
            NativeFieldOccurrence::through(s, incoming)
        } else {
            NativeFieldOccurrence::entering(incoming)
        };
        let next = f.advance_resident(&mut event).unwrap();
        if at == 0 {
            anchor = Some(f.retain_source(&next.source).unwrap());
        }
        last = Some(next.source);
    }
    last.unwrap()
}
fn returned<'c>(f: &NativeConstitutiveField<'c>) -> NativeMaterialContactResponse<'c> {
    let r = f
        .normalized_material_return(4, 2, SeriesAperture(32))
        .unwrap()
        .unwrap();
    let q = f
        .pull_back_material_source(&r, NativeMaterialPullbackMetric::RelativeEntropy)
        .unwrap();
    f.material_contact_response(q).unwrap()
}
fn enclosed(actual: &[ExactComplexWaveCurrent], center: &[ExactComplexWaveCurrent], radius: &Rat) {
    let error: Rat = actual
        .iter()
        .zip(center)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        error <= radius * radius,
        "squared error {error} exceeds radius squared {}",
        radius * radius
    );
}
fn decode(
    s: &ResidentSurface<'_>,
    v: &ResidentSection<'_>,
    g: u32,
) -> Vec<ExactComplexWaveCurrent> {
    let w = wides(&s.detach_section(v, 64).unwrap().intervals).unwrap();
    let scale = BigInt::one() << g;
    w.chunks_exact(2)
        .map(|v| {
            ExactComplexWaveCurrent::new(
                Rat::new(v[0].into(), scale.clone()),
                Rat::new(v[1].into(), scale.clone()),
            )
        })
        .collect()
}

#[test]
#[ignore = "requires CUDA; paired adjoint, finite mixed successor, journal recovery and refusal"]
fn material_contact_response_reaches_its_producer_and_changes_subsequent_conduct() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = make(&surface);
    let next = populate(&mut field);
    let census = field.census();
    let response = returned(&field);
    assert_eq!(field.census().section_read_outs, census.section_read_outs);
    let reading = response.inspect().unwrap();
    let k = response.query.contacts;
    let d = 6 * field.nodes();
    let map = decode(&surface, &response._producing.map, 72)
        .chunks(d / 2)
        .take(k)
        .map(|v| v.to_vec())
        .collect::<Vec<_>>();
    let raw = wides(
        &surface
            .detach_section(&response._forward, 64)
            .unwrap()
            .intervals,
    )
    .unwrap();
    let scale = BigInt::one() << 72u32;
    let waves = |v: &[i128]| {
        v.chunks_exact(2)
            .map(|v| {
                ExactComplexWaveCurrent::new(
                    Rat::new(v[0].into(), scale.clone()),
                    Rat::new(v[1].into(), scale.clone()),
                )
            })
            .collect::<Vec<_>>()
    };
    let incoming = waves(&raw[4 * (d + 1)..4 * (d + 1) + d]);
    let before = field.history[2]
        .resident()
        .unwrap()
        .operative
        .as_ref()
        .unwrap();
    let mut internal = decode(&surface, &before.b, 72);
    internal.truncate(before.count);
    internal.resize(k, ExactComplexWaveCurrent::zero());
    let producer = PairedJunctionLinearization::at(map, &incoming, &internal).unwrap();
    let midpoint = |xs: &[crate::exact_value::ExactInterval]| {
        xs.chunks_exact(2)
            .map(|v| {
                ExactComplexWaveCurrent::new(
                    (&v[0].lower + &v[0].upper) / Rat::from_integer(2.into()),
                    (&v[1].lower + &v[1].upper) / Rat::from_integer(2.into()),
                )
            })
            .collect::<Vec<_>>()
    };
    let reference = producer
        .pullback(
            &midpoint(&reading.query.outgoing_current),
            &midpoint(&reading.query.internal_current),
        )
        .unwrap();
    enclosed(
        &reference.source,
        &reading.incoming_source.center,
        &reading.incoming_source.radius,
    );
    enclosed(
        &reference.incoming_internal,
        &reading.incoming_internal.center,
        &reading.incoming_internal.radius,
    );
    enclosed(
        &reference.potential_covector,
        &reading.contact_covector.port_factors[0],
        &reading.potential_covector_radius,
    );
    let mut expected = Vec::new();
    let mut actual = Vec::new();
    for i in 0..k {
        expected.extend(reference.contacts.contact(i).unwrap());
        actual.extend(reading.contact_covector.contact(i).unwrap());
    }
    enclosed(&expected, &actual, &reading.contact_covector_radius);
    let norm: Rat = actual.iter().map(|v| v.norm_square()).sum();
    assert!(norm > &reading.contact_covector_radius * &reading.contact_covector_radius);
    let old = field.stage_operative_contacts().unwrap().inspect().unwrap();
    let prior = field.census();
    field.apply_material_contact_response(&response).unwrap();
    assert_eq!(field.census().section_read_outs, prior.section_read_outs);
    let changed = field.stage_operative_contacts().unwrap().inspect().unwrap();
    assert_ne!(changed.contacts, old.contacts);
    assert_ne!(changed.covariance, old.covariance);
    assert_ne!(changed.aggregate.center, old.aggregate.center);
    assert_eq!(changed.internal.center, old.internal.center); // constrained input-current response
    assert_eq!(changed.births, old.births);
    assert_eq!(changed.staged_returns, old.staged_returns + 1);
    // The response decoder must recover the producing map through the actual installed journal.
    let recovered = returned(&field).inspect().unwrap();
    assert_eq!(
        serde_json::to_value(&reading).unwrap(),
        serde_json::to_value(&recovered).unwrap()
    );
    let rest = field.rest(&[Some(&next)], &[]).unwrap();
    assert!(matches!(
        field.apply_material_contact_response(&response),
        Err(Error::ForeignOccurrence)
    ));
    assert_eq!(rest, field.rest(&[Some(&next)], &[]).unwrap());
    let mut event = NativeFieldOccurrence::through(next, vec![phase(0, 1), phase(1, 1)]);
    field.advance_resident(&mut event).unwrap();
    let changed_forward = field
        .inspect_contextual_material_transport(5)
        .unwrap()
        .unwrap()
        .forward;
    // Independently found sibling, not a clone of a continuing ecology.
    let mut sibling = make(&surface);
    let next = populate(&mut sibling);
    sibling
        .advance_resident(&mut NativeFieldOccurrence::through(
            next,
            vec![phase(0, 1), phase(1, 1)],
        ))
        .unwrap();
    let unchanged = sibling
        .inspect_contextual_material_transport(5)
        .unwrap()
        .unwrap()
        .forward;
    let difference: Rat = changed_forward
        .center
        .iter()
        .zip(&unchanged.center)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        difference
            > (&changed_forward.radius + &unchanged.radius)
                * (&changed_forward.radius + &unchanged.radius)
    );
    drop(field);
    drop(response);
    drop(sibling);
    let (mut restored, mut sources, _) = NativeConstitutiveField::remount(&surface, rest).unwrap();
    let next = sources[0].take().unwrap();
    restored
        .advance_resident(&mut NativeFieldOccurrence::through(
            next,
            vec![phase(0, 1), phase(1, 1)],
        ))
        .unwrap();
    assert_eq!(
        restored
            .inspect_contextual_material_transport(5)
            .unwrap()
            .unwrap()
            .forward,
        changed_forward
    );
}

#[test]
#[ignore="requires CUDA; exact deposited coefficient, retained projection defect and continuation"]
fn dyadic_contact_deposit_retains_its_defect_and_continues(){
    let readout=ResidentReadout::new().unwrap();let surface=ResidentSurface::on(&readout).unwrap();
    let mut field=make(&surface);let mut next=populate(&mut field);
    let response=returned(&field);let old=field.stage_operative_contacts().unwrap().inspect().unwrap();
    let r=response.inspect().unwrap();
    assert!(r.contact_covector_radius>Rat::from_integer(0.into()));
    let before=field.census();
    field.apply_material_contact_realization(&response,NativeContactRealization::DyadicDeposit).unwrap();
    assert_eq!(field.census().section_read_outs,before.section_read_outs);
    let after=field.stage_operative_contacts().unwrap().inspect().unwrap();
    assert_eq!(after.contacts_radius,old.contacts_radius);
    assert_eq!(after.internal.radius,old.internal.radius);
    let deposit=field.inspect_contact_deposit(0).unwrap();
    assert_eq!(deposit.realization,NativeContactRealization::DyadicDeposit);
    assert_eq!(deposit.unrounded_covector_radius,r.contact_covector_radius);
    assert!(deposit.numerical_projection_residual_norm_square>Rat::from_integer(0.into()));
    for i in 0..response.query.contacts {
        let unrounded=r.contact_covector.contact(i).unwrap();
        for j in 0..unrounded.len(){
            assert_eq!(after.contacts[i][j].subtract(&old.contacts[i][j]),
                unrounded[j].add(&deposit.numerical_projection_residual[i][j]));
        }
    }
    // The original response and source retain their nonzero comparison defect after adoption.
    assert_eq!(response.inspect().unwrap().contact_covector_radius,deposit.unrounded_covector_radius);
    let rest=field.rest(&[Some(&next)],&[]).unwrap();drop(response);drop(next);drop(field);
    let (mut field,mut sources,_)=NativeConstitutiveField::remount(&surface,rest).unwrap();next=sources[0].take().unwrap();
    assert_eq!(serde_json::to_value(field.inspect_contact_deposit(0).unwrap()).unwrap(),serde_json::to_value(deposit).unwrap());
    for at in 5..40 {
        let event=field.advance_resident(&mut NativeFieldOccurrence::through(next,
            vec![phase((at%3) as i64,1),phase(1,-((at%2) as i64))])).unwrap();
        next=event.source;
        let normalized=field.normalized_material_return(at,2,SeriesAperture(32)).unwrap().unwrap();
        let query=field.pull_back_material_source(&normalized,NativeMaterialPullbackMetric::RelativeEntropy).unwrap();
        let response=field.material_contact_response(query).unwrap();
        field.apply_material_contact_realization(&response,NativeContactRealization::DyadicDeposit).unwrap();
    }
    let state=field.stage_operative_contacts().unwrap().inspect().unwrap();
    assert_eq!(state.contacts_radius,old.contacts_radius);
    assert_eq!(state.staged_returns,36);
    let wire=field.junction.as_ref().unwrap().operative.as_ref().unwrap().wire();
    assert!(wire.return_frames.iter().all(|r|r.realization==NativeContactRealization::DyadicDeposit));
    // Older frames with no realization field keep the original enclosure contract.
    let legacy:super::super::rest::OperativeReturnFrame=serde_json::from_str("{\"at_cut\":1,\"contact_count\":0}").unwrap();
    assert_eq!(legacy.realization,NativeContactRealization::EnclosedFlow);
    drop(field);
    // A non-dyadic birth already has an enclosure. A later exact deposit must not erase it.
    let mut field=make(&surface);let mut next=None;
    for at in 0..5 {
        let input=vec![NativePhaseCurrent::new(1+(at%2),1,3).unwrap(),NativePhaseCurrent::new(1,-1,7).unwrap()];
        let mut event=match next.take(){Some(source)=>NativeFieldOccurrence::through(source,input),None=>NativeFieldOccurrence::entering(input)};
        next=Some(field.advance_resident(&mut event).unwrap().source);
    }
    let response=returned(&field);let before=field.stage_operative_contacts().unwrap().inspect().unwrap();
    assert!(before.contacts_radius>Rat::from_integer(0.into()));
    field.apply_material_contact_realization(&response,NativeContactRealization::DyadicDeposit).unwrap();
    let after=field.stage_operative_contacts().unwrap().inspect().unwrap();
    assert_eq!(after.contacts_radius,before.contacts_radius);
    assert_eq!(after.internal.radius,before.internal.radius);
}
