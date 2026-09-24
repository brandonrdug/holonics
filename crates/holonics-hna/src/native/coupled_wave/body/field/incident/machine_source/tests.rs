use super::super::machine_receiving::GeneratorPhasePort;
use super::*;
use crate::native::field_geometry::machine::{
    ClockSpec, GeneratorMachineSpec, GeneratorSiteSpec, MachineUnitsSpec, PhaseSpec,
};
use num_bigint::BigInt;
use holonics::geometry::{AffineMap3, Rat, RatVec3};

fn r(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn machine() -> CompiledGeneratorMachine {
    let site = |id: &str, source: bool| GeneratorSiteSpec {
        id: id.into(),
        angular: RatVec3::zero(),
        advance: RatVec3::zero(),
        initial: RatVec3::zero(),
        phase: PhaseSpec {
            parameter: r(0),
            extra_turns: 0,
            origin_exponent: 7,
            step: AffineMap3::identity(),
            period: None,
        },
        clock: ClockSpec {
            lineage: "episode".into(),
            duration: r(1),
            unit: "s".into(),
        },
        source,
        receiver: !source,
        material: None,
    };
    GeneratorMachineSpec::declare(
        "world",
        MachineUnitsSpec {
            spatial: std::array::from_fn(|_| "length".into()),
            current: std::array::from_fn(|_| "length".into()),
        },
        vec![site("a", true), site("b", false)],
        vec![],
        vec![],
    )
    .expect("machine")
    .compile()
    .expect("compiled machine")
}

fn binding() -> GeneratorSourceBinding {
    GeneratorSourceBinding {
        contact_kinds: vec![],
        offsets: vec![],
        source_id: "episode-1".into(),
        clock: ClockSpec {
            lineage: "episode".into(),
            duration: r(1),
            unit: "s".into(),
        },
        clocks: vec![
            GeneratorPhasePort {
                site_id: "a".into(),
                origin_exponent: 2,
                step_exponent: 1,
            },
            GeneratorPhasePort {
                site_id: "b".into(),
                origin_exponent: -1,
                step_exponent: 2,
            },
        ],
        injection_sites: vec!["a".into()],
    }
}

#[test]
fn binding_covers_sites_and_retains_clock_witnesses() {
    let machine = machine();
    let witnesses = binding().validate_scope(&machine, 3, 4).expect("binding");
    assert_eq!(witnesses.len(), 2);
    assert_eq!(witnesses[0].first_exponent, 7 + 2 + 3);
    assert_eq!(witnesses[0].last_exponent, 7 + 2 + 6);
    assert_eq!(witnesses[1].first_exponent, 7 - 1 + 6);
    assert_eq!(witnesses[1].last_exponent, 7 - 1 + 12);
}

#[test]
fn binding_rejects_non_source_injection_and_missing_clock_site() {
    let machine = machine();
    let mut invalid = binding();
    invalid.injection_sites = vec!["b".into()];
    assert!(invalid.validate_scope(&machine, 0, 1).is_err());
    let mut invalid = binding();
    invalid.clocks.pop();
    assert!(invalid.validate_scope(&machine, 0, 1).is_err());
}

#[test]
#[ignore = "requires CUDA; verifies one fixed action row per site is reused across events"]
fn source_maps_mount_one_fixed_step_row_per_site() {
    let readout = holonic_engine::embedding_fiber::ResidentReadout::new().unwrap();
    let surface = holonic_engine::resident_section::ResidentSurface::on(&readout).unwrap();
    let maps = MachineSourceMaps::new(
        &surface,
        &machine(),
        &binding(),
        4,
        3,
        holonic_engine::resident_section::ResidentGrain(32),
    )
    .unwrap();
    assert_eq!(maps.coefficients.rows(), maps.site_count());
    assert_eq!(maps.source_count(), 3);
    assert_eq!(maps.next_event(), 0);
}

/// Host-exact law: the composite powers reproduce `N` stepped injections exactly,
/// `L^N q₀ + Σ_k L^(N−1−k) E_k = (… (L q₀ + E_0) …)`, under a nonidentity rotation with a
/// translation-bearing step. The current is a tangent: the translation acts only on the
/// configuration chart `U^N`.
#[test]
fn moment_powers_equal_repeated_steps_exactly() {
    use holonics::geometry::cayley_rotation_z;
    let step = AffineMap3 {
        linear: cayley_rotation_z(&(r(1) / r(2))),
        translation: RatVec3::new(r(1) / r(16), r(-3), r(1) / r(5)),
    };
    let still = AffineMap3 {
        linear: cayley_rotation_z(&(r(1) / r(3))),
        translation: RatVec3::zero(),
    };
    let n = 11usize;
    let cells = (0..n as i64)
        .map(|k| RatVec3::new(r(k % 5 + 1), r(2 - k % 3), r(k % 7) / r(4)))
        .collect::<Vec<_>>();
    let q0 = RatVec3::new(r(7), r(-2), r(3) / r(8));
    let powers = moment_powers(&[still.clone(), step.clone()], &[1], n).unwrap();
    let mut stepped = q0.clone();
    for cell in &cells {
        stepped = step.linear.apply(&stepped).add(cell);
    }
    let mut closed = powers.standing()[1].apply(&q0);
    for (k, cell) in cells.iter().enumerate() {
        closed = closed.add(&powers.injection(0, n - 1 - k).unwrap().apply(cell));
    }
    assert_eq!(stepped, closed);
    // Powers exist only for injection sites; the standing covers every site.
    assert!(powers.injection(1, 0).is_none());
    assert_eq!(powers.standing().len(), 2);
    assert_eq!(
        powers.configuration()[0],
        super::super::machine_receiving::signed_affine_power(&still, n as i64).unwrap()
    );
    // Chart separation: the standing current carries no translation, the configuration does.
    assert_eq!(powers.standing()[1].translation, RatVec3::zero());
    assert_eq!(
        powers.configuration()[1],
        super::super::machine_receiving::signed_affine_power(&step, n as i64).unwrap()
    );
    assert_eq!(
        powers.standing()[1].linear,
        powers.configuration()[1].linear
    );
    // With no source, the standing current keeps its norm under the rotating step however
    // many steps are taken, while the configuration moves with the translation.
    let norm = |v: &RatVec3| &v.x * &v.x + &v.y * &v.y + &v.z * &v.z;
    let lifted = moment_powers(&[step.clone()], &[0], 128).unwrap();
    assert_eq!(norm(&lifted.standing()[0].apply(&q0)), norm(&q0));
    assert_ne!(norm(&lifted.configuration()[0].apply(&q0)), norm(&q0));
    // A permutation of the passage changes the moment under the rotating phase.
    let permuted = [0usize, 2, 1, 3]
        .iter()
        .map(|&k| cells[k].clone())
        .collect::<Vec<_>>();
    let moment = |cells: &[RatVec3]| {
        let powers = moment_powers(&[step.clone()], &[0], cells.len()).unwrap();
        cells
            .iter()
            .enumerate()
            .fold(RatVec3::zero(), |acc, (k, cell)| {
                acc.add(
                    &powers
                        .injection(0, cells.len() - 1 - k)
                        .unwrap()
                        .apply(cell),
                )
            })
    };
    assert_ne!(moment(&cells[..4]), moment(&permuted));
}
