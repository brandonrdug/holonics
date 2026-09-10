use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::NativeFieldRest;

fn field<'c>(surface: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let mut f = NativeConstitutiveField::found_with_enclosed_junction(
        surface,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
        ResidentGrain(72),
    )
    .unwrap();
    f.enable_material_transport_source(NativeMaterialTransportSource::OperativeNormal)
        .unwrap();
    f.enable_causal_contact_propagation().unwrap();
    f
}
fn waves(values: &[crate::exact_value::ExactInterval]) -> Vec<ExactComplexWaveCurrent> {
    let two = Rat::one() + Rat::one();
    values
        .chunks_exact(2)
        .map(|v| {
            ExactComplexWaveCurrent::new(
                (&v[0].lower + &v[0].upper) / &two,
                (&v[1].lower + &v[1].upper) / &two,
            )
        })
        .collect()
}
fn contains(
    expected: &[ExactComplexWaveCurrent],
    actual: &[ExactComplexWaveCurrent],
    radius: &Rat,
) {
    assert_eq!(expected.len(), actual.len());
    let square = expected
        .iter()
        .zip(actual)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum::<Rat>();
    assert!(
        square <= radius * radius,
        "complete current/covector lies outside retained radius"
    );
}
fn respond(f: &mut NativeConstitutiveField<'_>, at: usize) {
    if let Some(query) = f.pull_back_material_current(at).unwrap() {
        let response = f.material_contact_response(query).unwrap();
        f.apply_material_contact_realization(&response, NativeContactRealization::DyadicDeposit)
            .unwrap();
    }
}

#[test]
#[ignore = "requires CUDA; one live propagation/reflection/return, source regeneration and continuing checkpoint"]
fn live_causal_propagation_returns_the_complete_composition_and_restarts() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut f = field(&surface);
    let mut latest = None;
    let mut inputs = Vec::new();
    let mut changed_by_propagation=false;
    let mut producers = Vec::new();
    for (at, (real, imaginary)) in [(1, 1), (0, 1), (-1, 0), (1, -1), (1, 0), (0, -1)]
        .into_iter()
        .enumerate()
    {
        let before = f.stage_operative_contacts().unwrap().inspect().unwrap();
        let reference = CausalContactPropagation::at_enclosed(
            &before.births,
            &before.contacts,
            &before.contacts_radius,
            &before.internal,
            before.fractional_bits,
        )
        .unwrap();
        changed_by_propagation|=reference.internal.center!=before.internal.center;
        inputs.push(before.internal.clone());
        let incoming = vec![NativePhaseCurrent::new(real, imaginary, 3).unwrap()];
        let mut event = match latest.take() {
            Some(source) => NativeFieldOccurrence::through(source, incoming),
            None => NativeFieldOccurrence::entering(incoming),
        };
        let census = f.census();
        let next = f.advance_resident(&mut event).unwrap();
        assert_eq!(f.census().section_read_outs, census.section_read_outs);
        let after = f.stage_operative_contacts().unwrap().inspect().unwrap();
        producers.push(after.contacts.clone());
        let actual = f.inspect_operative_reflection(at).unwrap().unwrap();
        let mut arrived = reference.internal.center;
        arrived.resize(after.contacts.len(), ExactComplexWaveCurrent::zero());
        let reflected = PairedJunctionLinearization::at(
            after.contacts.clone(),
            &actual.source.center,
            &arrived,
        )
        .unwrap();
        assert!(actual.outgoing.contains(reflected.outgoing()));
        assert!(after.internal.contains(reflected.internal()));
        if let Some(query) = f.pull_back_material_current(at).unwrap() {
            let response = f.material_contact_response(query).unwrap();
            let reading = response.inspect().unwrap();
            assert!(reading.propagation_contacts.is_some());
            let source = next.lineage.observed_source().unwrap();
            let old = inputs[source].center.len();
            let d = producers[source].clone();
            let word = CausalContactPropagation::at(
                &before.births[..old],
                d[..old].to_vec(),
                &inputs[source].center,
            )
            .unwrap();
            let mut internal = word.internal().to_vec();
            internal.resize(d.len(), ExactComplexWaveCurrent::zero());
            let source_input = f
                .inspect_operative_reflection(source)
                .unwrap()
                .unwrap()
                .source;
            let paired =
                PairedJunctionLinearization::at(d.clone(), &source_input.center, &internal)
                    .unwrap();
            let outer = paired
                .pullback(
                    &waves(&reading.query.outgoing_current),
                    &waves(&reading.query.internal_current),
                )
                .unwrap();
            let inner = word.pullback(&outer.incoming_internal[..old]).unwrap();
            let mut expected_internal = outer.incoming_internal.clone();
            expected_internal[..old].clone_from_slice(&inner.incoming_internal);
            contains(
                &expected_internal,
                &reading.incoming_internal.center,
                &reading.incoming_internal.radius,
            );
            contains(
                &outer.source,
                &reading.incoming_source.center,
                &reading.incoming_source.radius,
            );
            let mut expected = Vec::new();
            let mut actual = Vec::new();
            for index in 0..d.len() {
                let mut gradient = outer.contacts.contact(index).unwrap();
                if index < old {
                    for (a, b) in gradient.iter_mut().zip(&inner.contacts[index]) {
                        *a = a.add(b);
                    }
                }
                expected.extend(gradient);
                actual.extend(reading.contact(index).unwrap());
            }
            contains(&expected, &actual, &reading.contact_covector_radius);
            let expected = serde_json::to_value(&reading).unwrap();
            {
                let op = f.junction.as_mut().unwrap().operative.as_mut().unwrap();
                op.recent_producers.clear();
                op.recent_propagations.clear();
            }
            let query = f.pull_back_material_current(at).unwrap().unwrap();
            let recovered = f.material_contact_response(query).unwrap();
            assert_eq!(
                serde_json::to_value(recovered.inspect().unwrap()).unwrap(),
                expected
            );
            let census = f.census();
            f.apply_material_contact_realization(
                &recovered,
                NativeContactRealization::DyadicDeposit,
            )
            .unwrap();
            assert_eq!(f.census().section_read_outs, census.section_read_outs);
        }
        latest = Some(next.source);
    }
    assert!(changed_by_propagation,"the live fixture must exercise nonidentity propagation");
    let archive = std::env::temp_dir().join(format!(
        "holonics-live-propagation-{}-{}.history",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    f.enable_history_archive(&archive).unwrap();
    f.archive_history_before(f.occurrence_count()).unwrap();
    let saved = f.rest(&[latest.as_ref()], &[]).unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let incoming = vec![NativePhaseCurrent::new(1, 1, 2).unwrap()];
    let source = f
        .advance_resident(&mut NativeFieldOccurrence::through(
            latest.take().unwrap(),
            incoming.clone(),
        ))
        .unwrap()
        .source;
    let at = f.occurrence_count() - 1;
    respond(&mut f, at);
    let expected = f.rest(&[Some(&source)], &[]).unwrap();
    drop(source);
    drop(f);
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let (mut f, mut sources, _) = NativeConstitutiveField::remount(&surface, saved).unwrap();
    let source = f
        .advance_resident(&mut NativeFieldOccurrence::through(
            sources[0].take().unwrap(),
            incoming,
        ))
        .unwrap()
        .source;
    respond(&mut f, at);
    assert_eq!(f.rest(&[Some(&source)], &[]).unwrap(), expected);
}

#[test]
#[ignore="requires CUDA; a propagation refusal cannot reach the field commit or consume the source"]
fn live_causal_propagation_refusal_preserves_the_complete_field() {
    let readout=ResidentReadout::new().unwrap();let surface=ResidentSurface::on(&readout).unwrap();
    let mut f=field(&surface);
    let first=f.advance_resident(&mut NativeFieldOccurrence::entering(vec![NativePhaseCurrent::unit()])).unwrap().source;
    let latest=f.advance_resident(&mut NativeFieldOccurrence::through(first,vec![NativePhaseCurrent::new(0,1,1).unwrap()])).unwrap().source;
    let saved=f.rest(&[Some(&latest)],&[]).unwrap();
    let op=f.junction.as_mut().unwrap().operative.as_mut().unwrap();
    let original=op.births[0].source;op.births[0].source=op.births[0].receiving;
    let mut event=NativeFieldOccurrence::through(latest,vec![NativePhaseCurrent::unit()]);
    assert!(f.advance_resident(&mut event).is_err());
    assert!(event.source_ref().is_some());
    f.junction.as_mut().unwrap().operative.as_mut().unwrap().births[0].source=original;
    assert_eq!(f.rest(&[event.source_ref()],&[]).unwrap(),saved);
}
