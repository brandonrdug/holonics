use super::*;

/// Law: normal-geometry validation admits exactly the moments (G, B, C) of a positive semidefinite
/// joint Gram and refuses any inconsistent cross moment or energy.
#[test]
fn complex_source_energy_validation_retains_its_null_fibre() {
    let q = |v: i64| Rat::from_integer(v.into());
    let z = |r, i| ExactComplexWaveCurrent::new(q(r), q(i));
    // x=(1,i), y=1: G=xx*, B=yx*, C=1, with a nontrivial complex source kernel.
    let mut v = NormalConstitution {
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
