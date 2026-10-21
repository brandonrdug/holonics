use super::material::product;
use super::*;
use num_traits::{One, Zero};
fn bounds() -> ContextualBounds {
    ContextualBounds {
        branches: 2,
        pending: 8,
        precision_bits: 20,
        rational_bits: 1024,
        max_features: 32,
        max_scalar_work: 1_000_000,
    }
}
fn z(v: i64) -> Complex {
    [integer(v), Rat::zero()]
}
#[test]
fn recovered_fixed_geometry_oracles_and_applied_residual() {
    for (c, expected, divisor) in [
        (1, vec![0, 1, 1, 1, 0, 1, 1], 2),
        (2, vec![1, 2, 1, 1, 1, 2, 1], 7),
    ] {
        let f = features(&[z(1)], &[z(c)], &[z(1)]);
        assert_eq!(f, expected.iter().map(|&x| z(x)).collect::<Vec<_>>());
        let m = EmpiricalMaterial::found(7, 1)
            .stage(&f, &[z(4 - c)], &bounds())
            .unwrap();
        assert_eq!(m.observations(), 1);
        assert_eq!(*m.target_energy(), integer((4 - c) * (4 - c)));
        for (j, x) in f.iter().enumerate() {
            assert_eq!(m.b[0][j], product(&z(4 - c), x));
            let ideal = &x[0] / integer(divisor);
            assert!((&m.applied[0][j][0] - ideal).abs() <= *m.coefficient_error_upper());
            assert!(m.applied[0][j][1].is_zero());
        }
        let nonzero = m.contract(&f).unwrap();
        assert_ne!(nonzero, vec![z(0)]);
        assert!(m.applied.iter().flatten().flat_map(|v| v.iter()).all(|q| {
            let den = q.denom();
            (den & (den - num_bigint::BigInt::one())).is_zero()
        }));
    }
}
#[test]
fn complex_normal_keeps_orientation_and_true_moments() {
    let f = vec![[integer(1), integer(1)], [integer(2), -integer(1)]];
    let y = vec![[integer(3), integer(2)]];
    let m = EmpiricalMaterial::found(2, 1)
        .stage(&f, &y, &bounds())
        .unwrap();
    assert_eq!(m.h[0][1], [integer(1), integer(3)]);
    assert_eq!(m.h[1][0], [integer(1), -integer(3)]);
    assert_eq!(m.b[0][0], [integer(5), -integer(1)]);
    assert_eq!(m.target_energy, integer(13));
    assert!(m.coefficient_error_upper() >= &Rat::zero());
}
