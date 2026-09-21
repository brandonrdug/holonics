use super::super::*;
use crate::ExactComplexWaveCurrent;
use crate::embedding_fiber::ResidentReadout;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

fn section<'c>(s: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            values.len(),
            ResidentGrain(0),
            i64::BITS,
            values.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}

fn enclosure_section<'c>(s: &'c ResidentSurface<'c>, values: &[i128]) -> ResidentSection<'c> {
    let words = values
        .iter()
        .flat_map(|value| {
            let bytes = value.to_le_bytes();
            [
                i64::from_le_bytes(bytes[..8].try_into().unwrap()),
                i64::from_le_bytes(bytes[8..].try_into().unwrap()),
            ]
        })
        .map(|word| (word, word))
        .collect::<Vec<_>>();
    s.mount_section_rest(
        &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), i64::BITS, words).unwrap(),
    )
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; enclosed forecast and staged material remain resident on the surface"]
fn enclosed_forecast_uses_retained_material_and_commit_checks_freshness() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let initial = section(&surface, &[0, 1, 3, 0]);
    let law = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 2, 1).unwrap();
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        ResidentConstitutiveCurrent::integers(&initial).unwrap(),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body.attach_normal_prediction(
        0,
        ResidentNormalMaterial::found_features(&surface, 5, 1, ResidentGrain(16)).unwrap(),
    )
    .map_err(|(_, error)| error)
    .unwrap();

    let scale = 1_i128 << 16;
    let source_section = enclosure_section(&surface, &[scale, 0, scale]);
    let observed_section = enclosure_section(&surface, &[2 * scale, -scale, scale]);
    let source = ResidentNormalEnclosureView {
        surface: &surface,
        section: &source_section,
        offset: 0,
        width: 2,
        grain: ResidentGrain(16),
    };
    let observed = ResidentNormalEnclosureView {
        surface: &surface,
        section: &observed_section,
        offset: 0,
        width: 2,
        grain: ResidentGrain(16),
    };
    let prepared = body
        .prepare_enclosed_material(
            0,
            source,
            ResidentConstitutiveCurrent::integers(&initial).unwrap(),
            observed,
        )
        .unwrap();
    let stale = body
        .prepare_enclosed_material(
            0,
            source,
            ResidentConstitutiveCurrent::integers(&initial).unwrap(),
            observed,
        )
        .unwrap();
    assert!(body.can_commit_field_reaction(&prepared));
    body.commit_field_reaction(prepared).unwrap();
    assert!(!body.can_commit_field_reaction(&stale));
    assert!(body.commit_field_reaction(stale).is_err());
    assert_eq!(
        body.predictive_material(0).unwrap().unwrap().observations(),
        1
    );

    let reads = surface.census().section_read_outs;
    let receipt = body
        .forecast_enclosed_reaction(
            0,
            source,
            ResidentConstitutiveCurrent::integers(&initial).unwrap(),
        )
        .unwrap();
    assert_eq!(surface.census().section_read_outs, reads);
    let producing_condition = surface
        .read_out(
            &receipt
                .producing_condition()
                .unwrap()
                .to_owned(&surface)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(receipt.material_observations(), 1);
    let output = receipt.output_view().inspect().unwrap();
    assert_eq!(output.center.len(), 1);
    assert!(output.radius >= Rat::from_integer(BigInt::from(0)));
    let cold = body
        .predictive_material(0)
        .unwrap()
        .unwrap()
        .inspect()
        .unwrap();
    let coefficients = &cold.material.coefficients[0];
    assert_eq!(coefficients.len(), 5);
    let i = ExactComplexWaveCurrent::new(Rat::zero(), Rat::one());
    let three = Rat::from_integer(BigInt::from(3));
    let a = coefficients[0]
        .add(&coefficients[3].multiply(&i))
        .add(&coefficients[4].scaled(&three));
    let c = coefficients[1]
        .multiply(&i)
        .add(&coefficients[2].scaled(&three));
    for s in [
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(1)), Rat::zero()),
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(2)), Rat::zero()),
        ExactComplexWaveCurrent::new(Rat::zero(), Rat::zero()),
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(1)), Rat::one()),
        ExactComplexWaveCurrent::new(
            Rat::from_integer(BigInt::from(1)),
            Rat::from_integer(BigInt::from(-1)),
        ),
    ] {
        let expected = [a.multiply(&s).add(&c)];
        assert!(
            output.contains(&expected),
            "applied enclosure lost exact face for {s:?}"
        );
    }
    let coefficient_norm = a.real.abs() + a.imaginary.abs();
    let rounding = Rat::new(3.into(), (1_i128 << 16).into());
    assert!(output.radius <= coefficient_norm + rounding);
    let applied_read = receipt
        .material
        .read_applied_bilinear(
            receipt.source_view(),
            receipt.producing_condition().unwrap(),
        )
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(applied_read, output);

    let later = body
        .prepare_enclosed_material(
            0,
            source,
            ResidentConstitutiveCurrent::integers(&initial).unwrap(),
            observed,
        )
        .unwrap();
    body.commit_field_reaction(later).unwrap();
    assert_eq!(receipt.output_view().inspect().unwrap(), output);
    assert_eq!(
        surface
            .read_out(
                &receipt
                    .producing_condition()
                    .unwrap()
                    .to_owned(&surface)
                    .unwrap()
            )
            .unwrap(),
        producing_condition
    );
    assert_eq!(
        body.predictive_material(0).unwrap().unwrap().observations(),
        2
    );
    // An actual condition input does not invent preimage-family evidence, but it must rest.
    let changed = section(&surface, &[1, 0, 2, 0]);
    body.receive_condition(ResidentConstitutiveCurrent::integers(&changed).unwrap())
        .unwrap();
    let expected = body
        .forecast_enclosed_reaction(0, source, body.condition())
        .unwrap()
        .output_view()
        .inspect()
        .unwrap();
    let saved = body.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    drop(body);
    let decoded =
        GeneratorNeighborhoodRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(decoded, saved);
    let resumed = decoded.remount(&surface).unwrap();
    assert_eq!(
        resumed
            .forecast_enclosed_reaction(0, source, resumed.condition())
            .unwrap()
            .output_view()
            .inspect()
            .unwrap(),
        expected
    );
}

#[test]
#[ignore = "requires CUDA; original producing c and contemporary standing use separate native paths"]
fn reaction_observation_at_keeps_producing_condition_and_returns_family() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let initial = section(&surface, &[1, 0, 3, 0]);
    let changed = section(&surface, &[0, 1, 11, 13]);
    let source = section(&surface, &[0, 0]);
    let target = section(&surface, &[1, 0]);
    fn c<'a, 'c>(p: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> { ResidentConstitutiveCurrent::integers(p).unwrap() }
    // At source zero, y=c_1 and c_2 is free. These are actual relation observations.
    let law = || {
        let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 2, 1).unwrap();
        for (h, y) in [([1, 0, 0, 0], [1, 0]), ([0, 0, 1, 0], [0, 0])] {
            let h = section(&surface, &h);
            let y = section(&surface, &y);
            law.advance_bilinear_contact(c(&source), c(&h), Some(c(&y)))
                .unwrap();
        }
        law
    };
    let normal = ResidentNormalMaterial::found_features(&surface, 5, 1, ResidentGrain(16))
        .unwrap()
        .stage_bilinear_observation(c(&source), c(&initial), c(&target))
        .unwrap();
    let expected_normal = normal
        .stage_bilinear_observation(c(&source), c(&initial), c(&target))
        .unwrap()
        .rest()
        .unwrap();
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law()],
        c(&initial),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body.attach_normal_prediction(0, normal)
        .unwrap_or_else(|(_, e)| panic!("{e:?}"));
    let expected_prediction = body
        .forecast_reaction_at_condition(0, c(&source), c(&initial))
        .unwrap()
        .inspect()
        .unwrap();
    let contemporary_prediction = body
        .forecast_reaction_at_condition(0, c(&source), c(&changed))
        .unwrap()
        .inspect()
        .unwrap();
    assert_ne!(expected_prediction, contemporary_prediction);
    let expected_formation = law()
        .advance_bilinear_contact(c(&source), c(&initial), Some(c(&target)))
        .unwrap()
        .inspect()
        .unwrap();
    body.receive_condition(c(&changed)).unwrap();
    let standing = surface
        .read_out(&body.condition().to_owned(&surface).unwrap())
        .unwrap();
    let step = body
        .receive_reaction_observation_at(0, c(&source), c(&initial), c(&target))
        .unwrap();
    assert_eq!(
        surface
            .read_out(&step.prior_condition.current().to_owned(&surface).unwrap())
            .unwrap(),
        standing
    );
    assert_eq!(step.prediction.inspect().unwrap(), expected_prediction);
    assert_eq!(
        step.formation.as_ref().unwrap().inspect().unwrap(),
        expected_formation
    );
    assert!(
        matches!(step.contact.as_ref().unwrap().family().inspect().unwrap(),
        ConditionPreimageReading::Compatible { ref directions, .. } if !directions.is_empty())
    );
    assert_eq!(
        body.predictive_material(0)
            .unwrap()
            .unwrap()
            .rest()
            .unwrap(),
        expected_normal
    );
}

#[test]
#[ignore = "requires CUDA; malformed source/condition/target must not publish any native state"]
fn reaction_observation_at_refusal_preserves_epoch_condition_and_material() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let initial = section(&surface, &[0, 1]);
    let source = section(&surface, &[1, 0]);
    let target = section(&surface, &[2, 3]);
    let wrong_condition = section(&surface, &[0, 1, 2, 3]);
    let wrong_target = section(&surface, &[2, 3, 4, 5]);
    let law = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 1, 1).unwrap();
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        ResidentConstitutiveCurrent::integers(&initial).unwrap(),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body.attach_normal_prediction(
        0,
        ResidentNormalMaterial::found_features(&surface, 3, 1, ResidentGrain(16)).unwrap(),
    )
    .unwrap_or_else(|(_, error)| panic!("{error:?}"));
    let before = body.rest().unwrap();

    assert!(
        body.receive_reaction_observation_at(
            0,
            ResidentConstitutiveCurrent::integers(&source).unwrap(),
            ResidentConstitutiveCurrent::integers(&wrong_condition).unwrap(),
            ResidentConstitutiveCurrent::integers(&target).unwrap(),
        )
        .is_err()
    );
    assert_eq!(body.rest().unwrap(), before);
    assert!(
        body.receive_reaction_observation_at(
            0,
            ResidentConstitutiveCurrent::integers(&source).unwrap(),
            ResidentConstitutiveCurrent::integers(&initial).unwrap(),
            ResidentConstitutiveCurrent::integers(&wrong_target).unwrap(),
        )
        .is_err()
    );
    assert_eq!(body.rest().unwrap(), before);
}
