use super::*;
use num_bigint::BigInt;

fn r(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn units() -> MachineUnitsSpec {
    MachineUnitsSpec {
        spatial: std::array::from_fn(|_| "length".into()),
        current: std::array::from_fn(|_| "length".into()),
    }
}

fn clock(lineage: &str) -> ClockSpec {
    ClockSpec {
        lineage: lineage.into(),
        duration: r(1),
        unit: "s".into(),
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
        clock: clock(id),
        source: id == "a",
        receiver: id == "b",
        material: Some([[r(2), r(0)], [r(0), r(3)]]),
    }
}

fn site_with_roles(id: &str, initial: RatVec3, source: bool, receiver: bool) -> GeneratorSiteSpec {
    let mut value = site(id, initial);
    value.source = source;
    value.receiver = receiver;
    value
}

fn response() -> SymmetricForm {
    SymmetricForm::from_rows(vec![
        vec![r(1), r(0), r(0)],
        vec![r(0), r(1), r(0)],
        vec![r(0), r(0), r(1)],
    ])
    .expect("symmetric response")
}

fn rate_port() -> ExactRatMatrix {
    let mut rows = vec![vec![r(0); 12]; 2];
    rows[0][0] = r(1); // receiver real channel
    rows[1][6] = r(1); // source real channel
    ExactRatMatrix::shaped(2, 12, rows).expect("rate port")
}

fn arc_with(
    id: &str,
    source: &str,
    receiver: &str,
    source_to_receiver: AffineMap3,
) -> GeneratorPairArcSpec {
    GeneratorPairArcSpec {
        id: id.into(),
        source: source.into(),
        receiver: receiver.into(),
        source_to_receiver,
        rate_port: rate_port(),
        response: response(),
        weight: r(1),
        clock: clock("ab"),
        parameter_units: ["a-param".into(), "b-param".into()],
    }
}

fn declaration() -> GeneratorMachineSpec {
    let ab = arc_with("ab", "a", "b", AffineMap3::identity());
    let bc = arc_with("bc", "b", "c", AffineMap3::identity());
    let ca = arc_with(
        "ca",
        "c",
        "a",
        AffineMap3 {
            linear: RatMat3::identity(),
            translation: RatVec3::from_i64(1, 0, 0),
        },
    );
    GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![
            site_with_roles("a", RatVec3::from_i64(0, 0, 0), true, false),
            site_with_roles("b", RatVec3::from_i64(0, 1, 0), false, true),
            site_with_roles("c", RatVec3::from_i64(0, 2, 0), false, false),
        ],
        vec![ab, bc, ca],
        vec![OrientedCellSpec {
            id: "cell".into(),
            edges: [
                CellEdgeSpec {
                    arc: "ab".into(),
                    reversed: false,
                },
                CellEdgeSpec {
                    arc: "bc".into(),
                    reversed: false,
                },
                CellEdgeSpec {
                    arc: "ca".into(),
                    reversed: false,
                },
            ],
        }],
    )
    .expect("machine declaration")
}

#[test]
fn current_action_realizes_affine_spatial_transport() {
    let source = RatVec3::from_i64(1, 2, 3);
    let receiver = RatVec3::from_i64(4, 5, 6);
    let transport = AffineMap3 {
        linear: RatMat3::identity(),
        translation: RatVec3::from_i64(3, 3, 3),
    };
    let action = CurrentAffineMap::between(&source, &receiver, &transport);
    assert_eq!(action.bias, RatVec3::zero());
    assert!(action.realizes(&source, &receiver, &transport));
    assert_eq!(
        action.spatial_residual(&source, &receiver, &transport),
        RatVec3::zero()
    );
}

#[test]
fn nonclosing_action_is_valid_but_claimed_closure_is_refused() {
    let mut nonclosing = site("a", RatVec3::zero());
    nonclosing.phase.step.translation = RatVec3::from_i64(1, 0, 0);
    nonclosing.phase.period = None;
    assert!(GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![nonclosing.clone()],
        vec![],
        vec![]
    )
    .is_ok());
    nonclosing.phase.period = Some(2);
    assert!(matches!(
        GeneratorMachineSpec::declare("world", units(), vec![nonclosing], vec![], vec![]),
        Err(MachineError::NotClosed { period: 2 })
    ));
}

#[test]
fn compile_constructs_helical_pair_and_cell_holonomy() {
    let compiled = declaration().compile().expect("compile machine");
    assert_eq!(compiled.sites().len(), 3);
    assert_eq!(compiled.arcs().len(), 3);
    assert_eq!(
        compiled.cells()[0].holonomy().translation,
        RatVec3::from_i64(1, 0, 0)
    );
    assert!(compiled.arcs()[0].interaction().rate_port().columns() == 12);
    assert!(compiled.arcs()[0].interaction().effective_slip().rows() == 3);
    assert!(compiled.trace_machine().is_some());
    assert_eq!(compiled.source_sites().count(), 1);
    assert_eq!(compiled.receiver_sites().count(), 1);
}

#[test]
fn pair_transports_source_into_receiver_frame_before_contact() {
    let mut source = site_with_roles("a", RatVec3::from_i64(1, 0, 0), true, false);
    source.angular = RatVec3::from_i64(0, 0, 1);
    let receiver = site_with_roles("b", RatVec3::from_i64(1, 4, 0), false, true);
    let transport = AffineMap3 {
        linear: relational_geometry::cayley_rotation_z(&r(1)),
        translation: RatVec3::from_i64(1, 2, 0),
    };
    let spec = GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![source, receiver],
        vec![arc_with("ab", "a", "b", transport.clone())],
        vec![],
    )
    .expect("declared pair");
    let compiled = spec.compile().expect("compiled pair");
    let pair = compiled.arcs()[0].interaction().pair();
    assert_eq!(
        pair.second().initial(),
        &transport.apply(&RatVec3::from_i64(1, 0, 0))
    );
    assert_eq!(pair.first().initial(), &RatVec3::from_i64(1, 4, 0));
    assert_eq!(compiled.arcs()[0].source(), "a");
    assert_eq!(compiled.arcs()[0].receiver(), "b");
}

#[test]
fn cells_must_reference_three_admitted_distinct_arcs() {
    let absent = GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![
            site("a", RatVec3::zero()),
            site("b", RatVec3::from_i64(0, 1, 0)),
            site("c", RatVec3::from_i64(0, 2, 0)),
        ],
        vec![arc_with("ab", "a", "b", AffineMap3::identity())],
        vec![OrientedCellSpec {
            id: "cell".into(),
            edges: [
                CellEdgeSpec {
                    arc: "ab".into(),
                    reversed: false,
                },
                CellEdgeSpec {
                    arc: "missing".into(),
                    reversed: false,
                },
                CellEdgeSpec {
                    arc: "ab".into(),
                    reversed: true,
                },
            ],
        }],
    );
    assert!(matches!(absent, Err(MachineError::UnknownArc(id)) if id == "missing"));
}

#[test]
fn invalid_response_is_rejected_at_declaration() {
    let invalid_response = SymmetricForm::from_rows(vec![
        vec![r(-1), r(0), r(0)],
        vec![r(0), r(1), r(0)],
        vec![r(0), r(0), r(1)],
    ])
    .expect("symmetric response");
    let mut invalid = arc_with("ab", "a", "b", AffineMap3::identity());
    invalid.response = invalid_response;
    let result = GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![
            site("a", RatVec3::zero()),
            site("b", RatVec3::from_i64(0, 1, 0)),
        ],
        vec![invalid],
        vec![],
    );
    assert!(matches!(
        result,
        Err(MachineError::ResponseNotPositiveSemidefinite { .. })
    ));
}

#[test]
fn spec_serialization_round_trip_reenters_validation() {
    let spec = declaration();
    let encoded = serde_json::to_string(&spec).expect("serialize");
    let decoded: GeneratorMachineSpec = serde_json::from_str(&encoded).expect("validated decode");
    assert_eq!(spec, decoded);
}

#[test]
fn malformed_rate_carrier_is_rejected_on_deserialize() {
    let spec = declaration();
    let mut value = serde_json::to_value(&spec).expect("serialize");
    value["arcs"][0]["rate_port"]["entries"] =
        serde_json::Value::Array((0..23).map(|_| serde_json::json!(0)).collect());
    let result = serde_json::from_value::<GeneratorMachineSpec>(value);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------------------------
// one clock and one generator
// ---------------------------------------------------------------------------------------------

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

/// A quarter turn about the z axis through the pivot `(1, 2, 0)`: period 4, `R + I` invertible.
fn quarter_turn_site(id: &str) -> GeneratorSiteSpec {
    let mut value = site(id, RatVec3::from_i64(3, -1, 5));
    value.phase = PhaseSpec {
        parameter: r(1),
        extra_turns: 2,
        origin_exponent: 0,
        step: AffineMap3::rotation_about(
            &RatVec3::from_i64(1, 2, 0),
            RatMat3::from_i64([[0, -1, 0], [1, 0, 0], [0, 0, 1]]),
        ),
        period: Some(4),
    };
    value.clock.duration = rational(1, 3);
    value
}

fn compiled_site(spec: GeneratorSiteSpec) -> CompiledGeneratorSite {
    GeneratorMachineSpec::declare("world", units(), vec![spec], vec![], vec![])
        .expect("declared site")
        .compile()
        .expect("compiled site")
        .sites()[0]
        .clone()
}

fn point(values: &[Rat]) -> RatVec3 {
    RatVec3::new(values[0].clone(), values[1].clone(), values[2].clone())
}

/// The wire form is byte-identical to the former derive and converts losslessly to and from the
/// declared engine clock and the unwound core clock at rest; a ring or reading is refused.
#[test]
fn clock_spec_is_the_lossless_wire_of_the_one_clock() {
    #[derive(Serialize)]
    struct FormerClockSpec {
        lineage: String,
        duration: Rat,
        unit: String,
    }
    let spec = ClockSpec {
        lineage: "site|clock".into(),
        duration: rational(5, 7),
        unit: "s".into(),
    };
    let former = FormerClockSpec {
        lineage: "site|clock".into(),
        duration: rational(5, 7),
        unit: "s".into(),
    };
    assert_eq!(
        serde_json::to_vec(&spec).unwrap(),
        serde_json::to_vec(&former).unwrap()
    );
    let clock = Clock::try_from(&spec).expect("declared clock");
    // The engine clock's wire is the spec's wire, byte for byte.
    assert_eq!(
        serde_json::to_vec(&clock).unwrap(),
        serde_json::to_vec(&spec).unwrap()
    );
    assert_eq!(ClockSpec::from(&clock), spec);
    let core = spec.core_clock().expect("core clock");
    assert_eq!(core.step(), &spec.duration);
    assert!(core.radices().is_empty() && core.is_at_rest());
    assert_eq!(
        ClockSpec::from_core("site|clock", core.clone(), "s").expect("wire of core"),
        spec
    );
    let ring = clock.on_ring(vec![BigUint::from(3u32)]).expect("ring");
    assert!(matches!(
        ClockSpec::from_core("site|clock", ring, "s"),
        Err(MachineError::Clock(
            InteractionRefusal::ClockNotDeclarable { levels: 1, .. }
        ))
    ));
    let mut ticked = core;
    ticked.advance(&BigUint::one());
    assert!(ClockSpec::from_core("site|clock", ticked, "s").is_err());
    // Deserialization still refuses an unknown field.
    let mut value = serde_json::to_value(&spec).unwrap();
    value["ring"] = serde_json::json!(3);
    assert!(serde_json::from_value::<ClockSpec>(value).is_err());
}

/// The whole machine wire is unchanged by carrying its clocks through the core clock: a
/// serialize/deserialize/serialize cycle is byte-identical, and each compiled clock's wire is
/// its declared spec.
#[test]
fn machine_wire_is_byte_identical_through_the_core_clock() {
    let spec = declaration();
    let first = serde_json::to_vec(&spec).unwrap();
    let decoded: GeneratorMachineSpec = serde_json::from_slice(&first).unwrap();
    assert_eq!(serde_json::to_vec(&decoded).unwrap(), first);
    let compiled = spec.compile().unwrap();
    for (declared, site) in spec.sites().iter().zip(compiled.sites()) {
        assert_eq!(ClockSpec::from_clock(site.clock()), declared.clock);
        assert_eq!(
            serde_json::to_vec(site.clock()).unwrap(),
            serde_json::to_vec(&declared.clock).unwrap()
        );
    }
    for (declared, arc) in spec.arcs().iter().zip(compiled.arcs()) {
        assert_eq!(
            ClockSpec::from_clock(arc.interaction().clock()),
            declared.clock
        );
    }
}

/// The core generator's Cayley tick is the site's phase action exactly, its advance reaches the
/// phase action's power, and its clock/lift readings are the odometer's carries on the closure
/// ring.
#[test]
fn core_generator_ticks_as_the_phase_action_and_counts_closure_windings() {
    let site = compiled_site(quarter_turn_site("q"));
    let generator = site.core_generator().expect("core generator");
    // The key is the situated screw's initial point; clock step h; lift = declared phase.
    assert_eq!(point(generator.initial()), *site.screw().initial());
    assert_eq!(generator.clock().step(), site.clock().duration());
    assert_eq!(generator.clock().radices(), &[BigUint::from(4u32)]);
    assert_eq!(generator.lift().phase(), site.phase());
    assert_eq!(generator.lift().winding(), &BigInt::from(2));
    // A is skew: the tick is a rotation (Cayley of a skew generator).
    let (a, _) = generator.transport().affine_parts().unwrap();
    for row in 0..3 {
        for column in 0..3 {
            let entry = |i: usize, j: usize| a.entries()[i * 3 + j].clone();
            assert_eq!(entry(row, column), -entry(column, row));
        }
    }
    // tick == phase action on several configurations.
    for probe in [
        RatVec3::from_i64(3, -1, 5),
        RatVec3::from_i64(0, 0, 0),
        RatVec3::new(rational(1, 2), rational(-7, 3), rational(2, 9)),
    ] {
        let ticked = generator
            .tick(&[probe.x.clone(), probe.y.clone(), probe.z.clone()])
            .expect("tick");
        assert_eq!(point(&ticked), site.phase_action().apply(&probe));
    }
    // advance(k) == T^k(key); jumps and lift winding are the odometer's carries.
    let key = site.screw().initial().clone();
    let mut stepwise = generator.clone();
    let mut configuration = generator.initial().to_vec();
    let mut jumps = BigUint::from(0u32);
    for k in 1u64..=11 {
        let step = stepwise.advance(&configuration, 1).expect("one tick");
        configuration = step.configuration;
        jumps += step.jumps;
        let power = affine_power(site.phase_action(), k as usize);
        assert_eq!(point(&configuration), power.apply(&key));
        let odometer =
            relational_geometry::Odometer::from_value(vec![BigUint::from(4u32)], &BigUint::from(k))
                .unwrap();
        assert_eq!(stepwise.clock().phase(), odometer.digits());
        assert_eq!(stepwise.clock().winding(), odometer.overflow_winding());
        assert_eq!(&jumps, odometer.overflow_winding());
        assert_eq!(
            stepwise.lift().winding(),
            &(BigInt::from(2) + BigInt::from(k / 4))
        );
        // Closure: the reached configuration is the power of the phase at the chart residue.
        let residue = affine_power(site.phase_action(), (k % 4) as usize);
        assert_eq!(point(&configuration), residue.apply(&key));
    }
    // A single advance of 11 ticks agrees with the stepwise one.
    let mut at_once = generator.clone();
    let reached = at_once.advance(generator.initial(), 11).expect("advance");
    assert_eq!(reached.configuration, configuration);
    assert_eq!(reached.jumps, BigUint::from(2u32));
    assert_eq!(at_once, stepwise);
    // The chart phase is unchanged by the counted jumps (lossless).
    assert_eq!(at_once.lift().chart(), site.phase().chart());
}

/// Period 1 is the unwound clock (every tick closes); the identity action has the zero generator.
#[test]
fn identity_site_is_an_unwound_zero_generator() {
    let site = compiled_site(site("a", RatVec3::from_i64(1, 2, 3)));
    let mut generator = site.core_generator().expect("core generator");
    assert!(generator.clock().radices().is_empty());
    let start = generator.initial().to_vec();
    let reached = generator.advance(&start, 5).unwrap();
    assert_eq!(reached.configuration, start);
    assert_eq!(reached.jumps, BigUint::from(5u32));
    assert_eq!(generator.lift().winding(), &BigInt::from(5));
    // The declared screw chart keeps the same key, clock and lift.
    let screw = site.declared_screw_generator().expect("screw generator");
    assert_eq!(screw.situated_screw().as_ref(), Some(site.screw()));
    assert_eq!(screw.clock(), site.core_generator().unwrap().clock());
    assert_eq!(screw.lift(), &site.phase_lift());
}

/// No closure witness, no ring: the generator is refused rather than claiming jumps. A half turn
/// has no rational Cayley generator.
#[test]
fn core_generator_refuses_an_unwitnessed_ring_and_a_half_turn() {
    let mut open = site("a", RatVec3::zero());
    open.phase.step.translation = RatVec3::from_i64(1, 0, 0);
    open.phase.period = None;
    assert!(matches!(
        compiled_site(open).core_generator(),
        Err(MachineError::NoClosureWitness(id)) if id == "a"
    ));
    let mut half = site("h", RatVec3::zero());
    half.phase.step = AffineMap3 {
        linear: RatMat3::from_i64([[-1, 0, 0], [0, -1, 0], [0, 0, 1]]),
        translation: RatVec3::zero(),
    };
    half.phase.period = Some(2);
    assert!(matches!(
        compiled_site(half).core_generator(),
        Err(MachineError::HalfTurnPhaseAction(id)) if id == "h"
    ));
}
