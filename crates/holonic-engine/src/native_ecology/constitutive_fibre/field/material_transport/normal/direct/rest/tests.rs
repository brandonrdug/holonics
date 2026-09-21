use super::*;
use crate::embedding_fiber::ResidentReadout;
fn point<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            v.len(),
            ResidentGrain(0),
            64,
            v.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn current<'a, 'c>(v: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(v).unwrap()
}
#[test]
#[ignore = "requires CUDA; exact normal geometry rests, mounts without refitting, and receives the next real current"]
fn complete_normal_material_roundtrip_and_next_observation() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut model = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(32)).unwrap();
    let x = point(&s, &[1, 0, 0, 0, 0, 0]);
    let y = point(&s, &[1, 0]);
    model.receive(current(&x), current(&y)).unwrap();
    let rest = model.rest().unwrap();
    let before = model.state_wire().unwrap();
    let mut wire = Vec::new();
    rest.write(&mut wire).unwrap();
    drop(model);
    let parsed = NormalMaterialRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(rest, parsed);
    let mut restored = parsed.remount(&s).unwrap();
    assert_eq!(restored.state_wire().unwrap(), before);
    restored.receive(current(&x), current(&y)).unwrap();
    assert_eq!(restored.observations(), 2);
    assert_ne!(restored.state_wire().unwrap(), before);
    restored.rest().unwrap();
    // A validly shaped but impossible energy or numerical witness cannot be mounted.
    let layout = NormalLayout::new(1, 1).unwrap();
    let mut malformed = before.clone();
    for entry in &mut malformed.intervals[layout.scalar_words_at() + 2 * MomentWire::WORDS
        ..layout.scalar_words_at() + 3 * MomentWire::WORDS]
    {
        *entry = (0, 0);
    }
    assert!(NormalMaterialRest::from_state_data(1, 1, ResidentGrain(32), 1, malformed).is_err());
    let mut wrong = before;
    wrong.intervals[0].0 += 1;
    wrong.intervals[0].1 += 1;
    assert!(NormalMaterialRest::from_state_data(1, 1, ResidentGrain(32), 1, wrong).is_err());
}

#[test]
#[ignore = "requires CUDA; nonzero prior keeps C0 separate from exterior Q_data and preserves the exact normal reference"]
fn nonzero_prior_rest_roundtrip_exposes_data_energy_and_exact_reference() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let q = |n: i64| Rat::from_integer(n.into());
    let one = ExactComplexWaveCurrent::one();
    let prior = NativeNormalPrior::from_coefficients(vec![vec![one.clone()]]).unwrap();
    let mut model = ResidentNormalMaterial::found_features_with_prior(
        &s,
        1,
        1,
        ResidentGrain(32),
        prior.clone(),
    )
    .unwrap();
    // The resident kernel keeps Q_data+C0 internally, while the exterior state
    // reports Q_data.  C0=1 and no observation means the reported energy is zero.
    assert_eq!(model.inspect().unwrap().target_energy, q(0));
    let rest = model.rest().unwrap();
    let mut wire = Vec::new();
    rest.write(&mut wire).unwrap();
    let parsed = NormalMaterialRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(parsed.prior(), Some(&prior));
    let mut corrupt = NormalMaterialRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    corrupt.header.prior.as_mut().unwrap().target_energy = q(2);
    assert!(corrupt.validate().is_err());
    let mut restored = parsed.remount(&s).unwrap();
    assert_eq!(restored.inspect().unwrap().target_energy, q(0));

    let x = point(&s, &[1, 0]);
    let y = point(&s, &[1, 0]);
    restored.receive(current(&x), current(&y)).unwrap();
    let state = restored.inspect().unwrap();
    assert_eq!(state.target_energy, q(1));
    // W0=1 and (x,y)=(1,1) give the exact normal reference W=1. The native
    // positive numerical proposal may differ; its stated radius must cover that difference.
    let difference = state.material.coefficients[0][0].subtract(&ExactComplexWaveCurrent::one());
    assert!(difference.norm_square() <= &state.material.radius * &state.material.radius);
    let residual = state.normal_residual().unwrap()[0][0].norm_square();
    assert!(residual <= &state.normal_residual_upper * &state.normal_residual_upper);
    restored.rest().unwrap().validate().unwrap();
}

#[test]
fn complex_source_energy_validation_retains_its_null_fibre() {
    let q = |v: i64| Rat::from_integer(v.into());
    let z = |r, i| ExactComplexWaveCurrent::new(q(r), q(i));
    // x=(1,i), y=1: G=xx*, B=yx*, C=1, with a nontrivial complex source kernel.
    let mut v = NativeNormalMaterialState {
        material: NativeFieldMaterialTransportState {
            coefficients: vec![vec![z(0, 0); 2]],
            radius: q(0),
        },
        source_normal: vec![vec![z(2, 0), z(0, -1)], vec![z(0, 1), z(2, 0)]],
        cross_source: vec![vec![z(1, 0), z(0, -1)]],
        source_normal_error: q(0),
        cross_source_error: q(0),
        target_energy: q(1),
        target_energy_error: q(0),
        normal_residual_upper: q(0),
    };
    validate_geometry(&v, 1).unwrap();
    v.cross_source[0][1] = z(0, 1);
    assert!(validate_geometry(&v, 1).is_err());
    v.cross_source[0][1] = z(0, -1);
    v.target_energy = q(0);
    assert!(validate_geometry(&v, 1).is_err());
    v.target_energy = q(2);
    assert!(validate_geometry(&v, 1).is_err());
    validate_geometry(&v, 2).unwrap();
    v.source_normal[0][0] = z(0, 0);
    assert!(validate_geometry(&v, 2).is_err());
}

#[test]
#[ignore = "requires CUDA; coupled normal coordinates and an isolated nonzero prior retain the same complete normal reference"]
fn normal_coupled_block_keeps_its_isolated_prior_and_full_residual() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let z = |r: i64, i: i64, d: i64| {
        ExactComplexWaveCurrent::new(Rat::new(r.into(), d.into()), Rat::new(i.into(), d.into()))
    };
    let prior =
        NativeNormalPrior::from_coefficients(vec![vec![z(0, 0, 1), z(2, -1, 1), z(0, 0, 1)]])
            .unwrap();
    let mut material =
        ResidentNormalMaterial::found_features_with_prior(&surface, 3, 1, ResidentGrain(32), prior)
            .unwrap();
    let x = point(&surface, &[1, 0, 0, 0, 1, 1]);
    let y = point(&surface, &[2, 3]);
    material.receive(current(&x), current(&y)).unwrap();
    let state = material.inspect().unwrap();
    // ||x||^2=3 and W0 x=0, so W=W0+y x*/4. The middle complex coordinate
    // remains an independent prior direction; the other two form the coupled block.
    let expected = [z(2, 3, 4), z(2, -1, 1), z(5, 1, 4)];
    let error: Rat = state.material.coefficients[0]
        .iter()
        .zip(&expected)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(error <= &state.material.radius * &state.material.radius);
    assert!(state.material.radius < Rat::new(1.into(), 1000.into()));
    let residual: Rat = state
        .normal_residual()
        .unwrap()
        .iter()
        .flatten()
        .map(ExactComplexWaveCurrent::norm_square)
        .sum();
    assert!(residual <= &state.normal_residual_upper * &state.normal_residual_upper);
    material.rest().unwrap().validate().unwrap();
}
