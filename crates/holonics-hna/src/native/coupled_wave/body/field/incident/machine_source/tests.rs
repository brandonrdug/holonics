use super::super::machine_receiving::GeneratorPhasePort;
use super::*;
use crate::native::field_geometry::machine::{
    ClockSpec, GeneratorMachineSpec, GeneratorSiteSpec, MachineUnitsSpec, PhaseSpec,
};
use num_bigint::BigInt;
use relational_geometry::{AffineMap3, Rat, RatVec3};

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
