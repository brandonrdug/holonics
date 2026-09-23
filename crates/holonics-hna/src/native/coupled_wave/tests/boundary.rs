use super::*;
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeConstitutiveField, NativeFieldCurrentSource, NativeFieldOccurrence, NativeJunctionSeed,
    NativePhaseCurrent,
};
use holonic_engine::ExactComplexWaveCurrent;

fn waves(value: &Value) -> Vec<ExactComplexWaveCurrent> {
    let values = value
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            num_rational::BigRational::new(
                v["numerator"].as_str().unwrap().parse().unwrap(),
                v["denominator"].as_str().unwrap().parse().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    values
        .chunks_exact(2)
        .map(|p| ExactComplexWaveCurrent::new(p[0].clone(), p[1].clone()))
        .collect()
}

fn step<'c>(field: &mut NativeConstitutiveField<'c>) -> NativeFieldCurrentSource<'c> {
    field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
    field.read_current_source().unwrap()
}

#[test]
#[ignore = "requires CUDA; real boundary and interior source families form material and enter joint HNN prediction"]
fn field_interiors_form_and_feed_the_coupled_prediction() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let grain = ResidentGrain(16);
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &s,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
        grain,
    )
    .unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    for input in [
        NativePhaseCurrent::new(0, 1, 1).unwrap(),
        NativePhaseCurrent::new(-1, 0, 1).unwrap(),
    ] {
        field
            .advance_resident(&mut NativeFieldOccurrence::through_anchor(
                &anchor,
                vec![input],
            ))
            .unwrap();
    }
    field.enable_operative_contacts().unwrap();
    let mut previous = field.read_current_source().unwrap();
    let mut now = step(&mut field);
    let n = now.enclosure().components() / 2;
    assert_eq!(n, 5); // Three boundary ports and two actually born internal currents.
    let mut material = ResidentNormalMaterial::found(&s, n, n, grain).unwrap();
    let reads = s.census().section_read_outs;
    for _ in 0..8 {
        let next = step(&mut field);
        assert!(previous.same_owner(&next));
        assert_eq!(previous.births(), next.births());
        let pair = previous.enclosure().join(now.enclosure()).unwrap();
        let source = pair.difference_source().unwrap();
        let observed = next.enclosure().difference(now.enclosure()).unwrap();
        material.receive(source.view(), observed.view()).unwrap();
        previous = now;
        now = next;
    }
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(material.observations(), 8);
    let fitted = material.inspect().unwrap();
    assert!(fitted.source_normal_error > num_rational::BigRational::from_integer(0.into()));
    // The initial condition is a unit coordinate of this explicitly condition-independent
    // Wave chart. The participating context is the actual boundary/interior state above.
    let law = material.read_applied_bilinear_relation(3 * n, 1).unwrap();
    let h = point(&s, &[1, 0]);
    let mut neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    neighborhood
        .attach_normal_prediction(0, material)
        .unwrap_or_else(|r| panic!("{:?}", r.reason));
    let pair = previous.enclosure().join(now.enclosure()).unwrap();
    let wave = ResidentNormalMaterial::found(&s, n, n, grain)
        .unwrap()
        .into_joint_difference_wave(pair.view())
        .unwrap()
        .with_neighborhood(neighborhood)
        .unwrap();
    let mut body = NativeCoupledBody::from_wave(wave);
    let delivery = std::time::Instant::now();
    let forecast = body
        .inspect_prospective(&[(0, WaveSourceReceiver::Direct); 2], true)
        .unwrap();
    let delivery_us = delivery.elapsed().as_micros();
    assert_eq!(forecast["reading"]["state_count"], 3);
    assert!(forecast["affine_joint"]["Plural"].is_object(), "{forecast}");
    for at in 0..2 {
        let p = waves(&forecast["states"][at]["projection"]["previous"]);
        let c = waves(&forecast["states"][at]["projection"]["current"]);
        let a = c
            .iter()
            .zip(&p)
            .map(|(c, p)| c.subtract(p))
            .chain(c.iter().cloned())
            .chain(p.iter().cloned())
            .collect::<Vec<_>>();
        let expected = fitted
            .material
            .coefficients
            .iter()
            .zip(&c)
            .map(|(row, c)| {
                row.iter()
                    .zip(&a)
                    .fold(c.clone(), |value, (m, a)| value.add(&m.multiply(a)))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            waves(&forecast["states"][at + 1]["projection"]["current"]),
            expected
        );
    }
    let epoch = body.epoch();
    let reads = s.census().section_read_outs;
    let pending=body.advance(0, WaveSourceReceiver::Direct, true).unwrap().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(body.epoch(), epoch + 1);
    let state = body.inspect_current().unwrap();
    assert_eq!(
        state["reading"]["projected_joint"].as_array().unwrap(),
        &forecast["reading"]["projected_joint"].as_array().unwrap()[42..62]
    );
    let saved = body.rest().unwrap();
    let mut wire = Vec::new();
    saved.write(&mut wire).unwrap();
    let mut resumed = SavedCoupledBody::read(&mut wire.as_slice(), wire.len() as u64)
        .unwrap()
        .remount(&s)
        .unwrap();
    assert_eq!(resumed.inspect_current().unwrap(), state);
    let actual_source=step(&mut field);
    let actual = actual_source.enclosure().inspect().unwrap();
    let prediction = waves(&forecast["states"][1]["projection"]["current"]);
    let residual = prediction
        .iter()
        .zip(&actual.center)
        .map(|(p, a)| p.subtract(a))
        .collect::<Vec<_>>();
    eprintln!("boundary transport: {n} complex state coordinates, 8 measured returns, 2 future states, delivery_us={delivery_us}; source_radius={}, actual_radius={}, prediction_minus_actual_center={}",pair.inspect().unwrap().radius,actual.radius,serde_json::to_string(&residual).unwrap());

    let before_epoch=body.epoch();let reads=s.census().section_read_outs;
    let started=std::time::Instant::now();
    let returned=body.observe(pending,actual_source.enclosure()).unwrap();
    let observation_us=started.elapsed().as_micros();
    assert_eq!(s.census().section_read_outs,reads);
    assert_eq!((returned.predecessor_observations,returned.successor_observations),(8,9));
    assert_eq!(body.epoch(),before_epoch);assert_eq!(body.pending_coupled_predictions(),0);
    assert_eq!(body.inspect_current().unwrap(),state);
    let source=returned.source().inspect().unwrap();
    let target=returned.target_increment().inspect().unwrap();
    let discrepancy=returned.discrepancy().inspect().unwrap();
    let squared_error=residual.iter().zip(&discrepancy.center).map(|(prediction_minus_actual,c)|{
        let delta=prediction_minus_actual.scaled(&num_rational::BigRational::from_integer((-1).into())).subtract(c);
        &delta.real*&delta.real+&delta.imaginary*&delta.imaginary
    }).sum::<num_rational::BigRational>();
    assert!(squared_error<=&discrepancy.radius*&discrepancy.radius);
    let after=body.affine_wave().unwrap().neighborhood().predictive_material(0).unwrap().unwrap().inspect().unwrap();
    for row in 0..n {for col in 0..3*n {
        assert_eq!(after.cross_source[row][col],fitted.cross_source[row][col]
            .add(&target.center[row].multiply(&source.center[col].conjugate())));
    }}
    // Rest directly after formation must retain the old held map alongside new M.
    let saved=body.rest().unwrap();let mut wire=Vec::new();saved.write(&mut wire).unwrap();
    resumed=SavedCoupledBody::read(&mut wire.as_slice(),wire.len() as u64).unwrap().remount(&s).unwrap();
    assert_eq!(resumed.inspect_current().unwrap(),state);
    let expected=body.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap();
    assert_eq!(resumed.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap(),expected);
    let held=body.affine_wave().unwrap().current().read_receiver().unwrap().inspect().unwrap()
        .projected_joint.unwrap().chunks_exact(2)
        .map(|v|ExactComplexWaveCurrent::new(v[0].clone(),v[1].clone())).collect::<Vec<_>>();
    let (p,c)=held.split_at(n);
    let a=c.iter().zip(p).map(|(c,p)|c.subtract(p)).chain(c.iter().cloned()).chain(p.iter().cloned()).collect::<Vec<_>>();
    let expected_current=after.material.coefficients.iter().zip(c).map(|(row,c)|{
        row.iter().zip(&a).fold(c.clone(),|v,(m,a)|v.add(&m.multiply(a)))
    }).collect::<Vec<_>>();
    assert_eq!(waves(&expected["states"][1]["projection"]["current"]),expected_current);
    eprintln!("boundary empirical return: field_cut={}, wave_epoch={}, material_observations=9, observation_us={observation_us}, source_radius={}, target_radius={}, discrepancy_radius={}",actual_source.field_cut(),body.epoch(),source.radius,target.radius,discrepancy.radius);
}

#[test]
#[ignore="requires CUDA; a live material response changes the conditional HNN reflection at the same bounded source"]
fn changing_operative_material_conditions_the_same_hnn_source(){
    use holonic_engine::native_ecology::constitutive_fibre::{NativeContactRealization,NativeMaterialTransportSource,ResidentNormalInput,ResidentNormalEnclosure};
    let ro=ResidentReadout::new().unwrap();let s=ResidentSurface::on(&ro).unwrap();let grain=ResidentGrain(24);
    let mut field=NativeConstitutiveField::found_with_enclosed_junction(&s,vec![NativeJunctionSeed{
        incoming_admittance:1,held_admittance:1,incoming_transport:NativePhaseCurrent::unit(),initial_held:NativePhaseCurrent::zero(),
    }],grain).unwrap();
    field.enable_material_transport_source(NativeMaterialTransportSource::OperativeNormal).unwrap();
    let mut predecessor=None;
    for input in [NativePhaseCurrent::new(4,0,1).unwrap(),NativePhaseCurrent::new(0,4,1).unwrap(),NativePhaseCurrent::new(-4,0,1).unwrap()]{
        let mut event=match predecessor.take(){Some(old)=>NativeFieldOccurrence::through(old,vec![input]),None=>NativeFieldOccurrence::entering(vec![input])};
        predecessor=Some(field.advance_resident(&mut event).unwrap().source);
    }
    let old=field.read_current_source().unwrap();let cut=field.occurrence_count();
    let n=old.enclosure().components()/2;let k=old.material().unwrap().unwrap().components()/2;
    assert_eq!((n,k),(5,6));let features=3*n+k+3*n*k;
    let mut material=ResidentNormalMaterial::found_features(&s,features,n,grain).unwrap();
    let zero=ResidentNormalInput::from(current(&point(&s,&vec![0;2*n]))).enclosure(&s,grain).unwrap();
    let mut xs=Vec::new();let mut ys=Vec::new();
    fn expose<'c>(source:&NativeFieldCurrentSource<'c>,s:&'c ResidentSurface<'c>,grain:ResidentGrain,n:usize,zero:&ResidentNormalEnclosure<'c>,xs:&mut Vec<ResidentNormalEnclosure<'c>>,ys:&mut Vec<ResidentNormalEnclosure<'c>>) {
        let h=source.material().unwrap().unwrap().read_exact_point().unwrap();
        for previous in [false,true] {for coordinate in 0..2*n {for sign in [-1,1] {
            let mut values=vec![0;2*n];values[coordinate]=sign*8;
            let pulse=ResidentNormalInput::from(current(&point(&s,&values))).enclosure(&s,grain).unwrap();
            let (p,c)=if previous {(pulse.view(),zero.view())}else{(zero.view(),pulse.view())};
            let pair=p.join(c).unwrap();let a=pair.difference_source().unwrap();
            let x=a.view().bilinear_features(ResidentConstitutiveCurrent::rational(&h).unwrap()).unwrap();
            let response=source.reflect(c).unwrap();let y=response.output().difference(c).unwrap();
            xs.push(x);ys.push(y);
        }}}
    }
    let reads=s.census().section_read_outs;expose(&old,&s,grain,n,&zero,&mut xs,&mut ys);
    // The actual latest observation has an earlier source with one born contact.
    // Probes above were read-only, so the material response is still at its valid cut.
    assert_eq!(field.occurrence_count(),cut);
    let query=field.pull_back_material_current(cut-1).unwrap().unwrap();
    let response=field.material_contact_response(query).unwrap();
    field.apply_material_contact_realization(&response,NativeContactRealization::DyadicDeposit).unwrap();
    let changed=field.read_current_source().unwrap();expose(&changed,&s,grain,n,&zero,&mut xs,&mut ys);
    assert_eq!(s.census().section_read_outs,reads);assert_eq!(field.occurrence_count(),cut);
    assert_eq!(old.births(),changed.births());
    assert_eq!(old.enclosure().inspect().unwrap().center,changed.enclosure().inspect().unwrap().center);
    assert_ne!(old.material().unwrap().unwrap().inspect().unwrap().center,changed.material().unwrap().unwrap().inspect().unwrap().center);
    let pairs=xs.iter().zip(&ys).map(|(x,y)|(x.view(),y.view())).collect::<Vec<_>>();
    let count=pairs.len() as u64;let fit=std::time::Instant::now();material.receive_many(&pairs).unwrap();let fit_us=fit.elapsed().as_micros();
    let h=old.material().unwrap().unwrap().read_exact_point().unwrap();let law=material.read_applied_bilinear_relation(3*n,k).unwrap();
    let mut local=ResidentGeneratorNeighborhood::with_shared_condition(vec![law],ResidentConstitutiveCurrent::rational(&h).unwrap(),ConditionContactMetric::UnitAdmittanceRealification).unwrap();
    local.attach_normal_prediction(0,material).unwrap_or_else(|r| panic!("{:?}", r.reason));
    let input=old.enclosure();let pair=zero.view().join(input).unwrap();
    let wave=ResidentNormalMaterial::found(&s,n,n,grain).unwrap().into_joint_difference_wave(pair.view()).unwrap().with_neighborhood(local).unwrap();
    let mut body=NativeCoupledBody::from_wave(wave);let held=body.inspect_current().unwrap();let epoch=body.epoch();
    let before=body.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap();
    let h=changed.material().unwrap().unwrap().read_exact_point().unwrap();let reads=s.census().section_read_outs;
    body.receive_condition(ResidentConstitutiveCurrent::rational(&h).unwrap()).unwrap();
    assert_eq!(s.census().section_read_outs,reads);assert_eq!(body.epoch(),epoch);assert_eq!(body.inspect_current().unwrap(),held);
    let after=body.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap();
    assert_ne!(before["states"][1]["projection"]["current"],after["states"][1]["projection"]["current"]);
    // The changed condition survives rest and remount exactly: the same current AND the same
    // prospective reading come back from the wire, with no readout and no re-fit.
    {
        let saved=body.rest().unwrap();let mut bytes=Vec::new();saved.write(&mut bytes).unwrap();
        let mut resumed=SavedCoupledBody::read(&mut bytes.as_slice(),bytes.len() as u64).unwrap().remount(&s).unwrap();
        assert_eq!(resumed.inspect_current().unwrap(),body.inspect_current().unwrap());
        assert_eq!(resumed.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap(),after);
    }
    let actual=changed.reflect(input).unwrap();let former=old.reflect(input).unwrap();
    assert_ne!(actual.output().inspect().unwrap().center,former.output().inspect().unwrap().center);
    let id=body.advance(0,WaveSourceReceiver::Direct,true).unwrap().unwrap();
    let reads=s.census().section_read_outs;
    let observation=std::time::Instant::now();let returned=body.observe(id,actual.output()).unwrap();let observation_us=observation.elapsed().as_micros();
    assert_eq!(s.census().section_read_outs,reads);assert_eq!((returned.predecessor_observations,returned.successor_observations),(count,count+1));
    let residual=returned.discrepancy().inspect().unwrap();
    let saved=body.rest().unwrap();let mut bytes=Vec::new();saved.write(&mut bytes).unwrap();
    let mut resumed=SavedCoupledBody::read(&mut bytes.as_slice(),bytes.len() as u64).unwrap().remount(&s).unwrap();
    assert_eq!(resumed.inspect_current().unwrap(),body.inspect_current().unwrap());
    // THE PROSPECTIVE READING AFTER THE COMMITTED STEP, IN THE FACTORED CHART.
    //
    // The committed step deposits the joint (z0,z1): 84 source coordinates over a rank-20
    // direction block whose entries are 48 octaves at this grain. Measured on the card, that
    // presentation is already reduced -- integer size reduction, LLL and the rational reduced
    // echelon form all return the same 48 octaves, because the subspace IS the graph of the
    // learned 48-octave step map over the anchor block. One further EXPANDED composition
    // therefore needs roughly 96 octaves per entry and cannot enter the int64 affine report
    // word at all; that arm still refuses, and its refusal is a property of the chart, not of
    // the relation. The same relation read in its FACTORED chart -- the retained word applied
    // to this family's own receiver point, in the wide carrier -- returns the reading. The
    // rebase is exact: every direction of this family moves the anchor, so the fibre over the
    // projected anchor is a single point and the joint minimum-norm receiver of (z0, L z0) is
    // exactly the image of this family's receiver point.
    let live=body.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap();
    assert_eq!(resumed.inspect_prospective(&[(0,WaveSourceReceiver::Direct)],true).unwrap(),live);
    assert_eq!(live["receiver_representation"],"generated-point-word");
    assert_eq!(live["reading"]["state_count"],2);
    assert_eq!(live["reading"]["support"],"Supported");
    // Nothing is free at a fixed anchor: that is the exact condition under which the factored
    // chart reproduces the expanded joint receiver rather than standing in for it.
    assert!(live["reading"]["anchor_independent_free"].as_array().unwrap().iter().all(|v|v==false));
    // The word's first state IS the committed current, coordinate for coordinate, so the
    // factored reading starts from this family's own receiver and not from some other point.
    let held_now=body.inspect_current().unwrap();
    let joint=live["reading"]["projected_joint"].as_array().unwrap();
    assert_eq!(held_now["reading"]["projected_joint"].as_array().unwrap().as_slice(),&joint[..2*n*2]);
    let (state0,state1)=(waves(&live["states"][0]["projection"]["current"]),waves(&live["states"][1]["projection"]["current"]));
    assert_eq!(state0.len(),n);assert_ne!(state0,state1);
    // The changed material conditions THIS reading too: the same word over the same committed
    // body, read before the condition arrived, is a different future.
    assert_ne!(live["states"][1]["projection"]["current"],before["states"][1]["projection"]["current"]);
    // BOUNDED STEP OVER STEP. Each factor of the word adds at most its own octave to the
    // reading; nothing accumulates the history of pivots that produced it. The measured
    // committed presentation supplies the bound -- no authored constant stands in for it.
    let bits=|v:&num_rational::BigRational|v.numer().bits().max(v.denom().bits());
    let octaves=|w:&[ExactComplexWaveCurrent]|w.iter().map(|c|bits(&c.real).max(bits(&c.imaginary))).max().unwrap_or(0);
    let factor_octaves=match body.affine_wave().unwrap().current().affine_relation().inspect().unwrap().predecessor_reading{
        holonic_engine::native_ecology::constitutive_fibre::ConstitutiveReading::Plural{directions,..}=>
            directions.iter().flatten().map(bits).max().unwrap_or(0),
        other=>panic!("the committed step deposits a plural family: {other:?}"),
    };
    let (zero_octaves,one_octaves)=(octaves(&state0),octaves(&state1));
    assert!(one_octaves<=zero_octaves+factor_octaves,
        "one factor added more than its own octave: {zero_octaves} -> {one_octaves} through {factor_octaves}");
    assert!(one_octaves<127,"the factored reading must stay inside the exact wide carrier: {one_octaves}");
    eprintln!("operative-condition HNN prospective after the committed step: read in the factored \
        chart, state0_max_octaves={zero_octaves}, state1_max_octaves={one_octaves}, factor_octaves={factor_octaves}");
    eprintln!("operative-condition HNN: state_complex={n}, condition_complex={k}, feature_complex={features}, training_returns={count}, material_returns=1, fit_us={fit_us}, observation_us={observation_us}, signed_discrepancy={}, discrepancy_radius={}",serde_json::to_string(&residual.center).unwrap(),residual.radius);
}
