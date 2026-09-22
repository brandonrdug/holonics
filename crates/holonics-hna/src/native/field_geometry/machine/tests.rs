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
