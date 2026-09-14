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
        .unwrap_or_else(|(_, e)| panic!("{e}"));
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
    body.advance(0, WaveSourceReceiver::Direct, false).unwrap();
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
    let actual = step(&mut field).enclosure().inspect().unwrap();
    let prediction = waves(&forecast["states"][1]["projection"]["current"]);
    let residual = prediction
        .iter()
        .zip(&actual.center)
        .map(|(p, a)| p.subtract(a))
        .collect::<Vec<_>>();
    eprintln!("boundary transport: {n} complex state coordinates, 8 measured returns, 2 future states, delivery_us={delivery_us}; source_radius={}, actual_radius={}, prediction_minus_actual_center={}",pair.inspect().unwrap().radius,actual.radius,serde_json::to_string(&residual).unwrap());
}
