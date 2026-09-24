use super::super::machine::{
    ClockSpec, GeneratorMachineSpec, GeneratorPairArcSpec, GeneratorSiteSpec, MachineUnitsSpec,
    PhaseSpec,
};
use super::*;
use holonics::exact_linear::ExactRatMatrix;
use holonics::exact_value::ExactInterval;
use holonics::inertia::SymmetricForm;
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::{AffineMap3, Rat, RatVec3};

fn r(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn units() -> MachineUnitsSpec {
    MachineUnitsSpec {
        spatial: std::array::from_fn(|_| "length".into()),
        current: std::array::from_fn(|_| "length".into()),
    }
}

fn site(id: &str, initial: RatVec3) -> GeneratorSiteSpec {
    GeneratorSiteSpec {
        id: id.into(),
        angular: RatVec3::zero(),
        advance: RatVec3::from_i64(0, 1, 0),
        initial,
        phase: PhaseSpec {
            parameter: r(0),
            extra_turns: 0,
            origin_exponent: 0,
            step: AffineMap3::identity(),
            period: Some(1),
        },
        clock: ClockSpec {
            lineage: id.into(),
            duration: r(1),
            unit: "s".into(),
        },
        source: id == "a",
        receiver: id == "b",
        material: None,
    }
}

fn rate_port() -> ExactRatMatrix {
    let mut rows = vec![vec![r(0); 12]; 2];
    rows[0][0] = r(1);
    rows[1][6] = r(1);
    ExactRatMatrix::shaped(2, 12, rows).expect("rate port")
}

fn arc(response: SymmetricForm, weight: Rat) -> GeneratorPairArcSpec {
    GeneratorPairArcSpec {
        id: "ab".into(),
        source: "a".into(),
        receiver: "b".into(),
        source_to_receiver: AffineMap3::identity(),
        rate_port: rate_port(),
        response,
        weight,
        clock: ClockSpec {
            lineage: "ab".into(),
            duration: r(1),
            unit: "s".into(),
        },
        parameter_units: ["receiver".into(), "source".into()],
    }
}

fn response(diagonal: [i64; 3]) -> SymmetricForm {
    SymmetricForm::from_rows(vec![
        vec![r(diagonal[0]), r(0), r(0)],
        vec![r(0), r(diagonal[1]), r(0)],
        vec![r(0), r(0), r(diagonal[2])],
    ])
    .expect("response")
}

fn factor_with_weight(response: SymmetricForm, weight: Rat) -> MachineFactor {
    let spec = GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![
            site("a", RatVec3::zero()),
            site("b", RatVec3::from_i64(0, 1, 0)),
        ],
        vec![arc(response, weight)],
        vec![],
    )
    .expect("machine")
    .compile()
    .expect("compiled machine");
    MachineFactor::from_arc(&spec.arcs()[0], 40).expect("factor")
}

fn factor(response: SymmetricForm, weight: i64) -> MachineFactor {
    factor_with_weight(response, r(weight))
}

fn native_gram(factor: &MachineFactor) -> ExactRatMatrix {
    let scale = dyadic_scale(factor.gram_error().grain);
    let rows = factor.native_rows();
    let mut entries = vec![vec![Rat::zero(); 12]; 12];
    for row in rows {
        for left in 0..12 {
            for right in 0..12 {
                entries[left][right] += Rat::from_integer(BigInt::from(row[left].center))
                    * Rat::from_integer(BigInt::from(row[right].center))
                    / (&scale * &scale);
            }
        }
    }
    ExactRatMatrix::new(entries).expect("native Gram")
}

#[test]
fn full_rank_square_root_rows_retain_algebraic_intervals_and_gram_bound() {
    let factor = factor(response([1, 1, 1]), 2);
    assert_eq!(factor.rank(), 3);
    assert_eq!(factor.native_rows().len(), 3);
    for (row, root) in factor.roots().iter().enumerate() {
        let Some(column) =
            (0..12).find(|column| !factor.rational_rows().get(row, *column).unwrap().is_zero())
        else {
            assert!(
                factor.native_rows()[row]
                    .iter()
                    .all(|x| x.center == 0 && x.radius == 0)
            );
            continue;
        };
        let expected =
            ExactInterval::point(factor.rational_rows().get(row, column).unwrap().clone())
                .times(&root.isolating_interval)
                .unwrap();
        assert!(
            factor.native_rows()[row][column]
                .contains_interval(&expected)
                .unwrap()
        );
    }
    let native = native_gram(&factor);
    let bound = factor.gram_error().interval().unwrap();
    for left in 0..12 {
        for right in 0..12 {
            let residual =
                factor.contact_form().get(left, right).unwrap() - native.get(left, right).unwrap();
            assert!(bound.lower <= residual && residual <= bound.upper);
        }
    }
    assert!(factor.factor_error().words > 0);
    assert!(factor.gram_error().words > 0);
    assert_ne!(factor.factor_error().words, factor.gram_error().words);
}

#[test]
fn tiny_positive_material_keeps_its_root_below_the_native_grid() {
    let tiny = Rat::new(BigInt::one(), BigInt::from(BigUint::one() << 240usize));
    let factor = factor_with_weight(response([0, 1, 0]), tiny);
    assert_eq!(factor.rank(), 1);
    let exact_root = Rat::new(BigInt::one(), BigInt::one() << 120usize);
    assert_eq!(factor.roots()[0].isolating_interval.lower, Rat::zero());
    assert!(factor.roots()[0].isolating_interval.upper > exact_root);
    assert!(factor.native_rows()[0].iter().any(|entry| entry.radius > 0));
}

#[test]
fn singular_response_keeps_three_structural_rows() {
    let factor = factor(response([0, 1, 0]), 1);
    assert_eq!(factor.rank(), 1);
    assert!(factor.native_rows()[1..].iter().all(|row| {
        row.iter()
            .all(|entry| entry.center == 0 && entry.radius == 0)
    }));
    assert_eq!(factor.response(), factor.response_reconstruction());
}

#[test]
fn rank_zero_response_returns_zero_rows_and_zero_form() {
    let factor = factor(response([0, 0, 0]), 7);
    assert_eq!(factor.rank(), 0);
    assert!(factor.metric().is_none());
    assert!(factor.native_rows().iter().all(|row| {
        row.iter()
            .all(|entry| entry.center == 0 && entry.radius == 0)
    }));
    assert!(factor.contact_form().entries().iter().all(Rat::is_zero));
    assert_eq!(factor.factor_error().words, 0);
    assert_eq!(factor.gram_error().words, 0);
}
