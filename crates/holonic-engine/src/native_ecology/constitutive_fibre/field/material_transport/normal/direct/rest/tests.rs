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
