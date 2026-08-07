use super::*;
use soma_membrane::SparseStandingSurface;

const TEST_SCHEMA: u64 = 0x5445_5354_4745_524d;
const INFORMANT_SCHEMA: u64 = 0x5445_5354_494e_464f;

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).unwrap()
}

fn germ(name: &str) -> ResonanceGerm {
    ResonanceGerm::new(
        fiber_from_bytes(TEST_SCHEMA, name.as_bytes()),
        RelationAtom::new(Cog::lit(7)).unwrap(),
    )
}

fn informant(name: &str, order: u64, germs: &[&str]) -> ResonanceOccurrence {
    ResonanceOccurrence::informant(
        fiber_from_bytes(INFORMANT_SCHEMA, name.as_bytes()),
        order,
        germs.iter().map(|name| germ(name)).collect(),
    )
    .unwrap()
}

#[test]
fn recurring_germs_condition_one_channel_and_leave_unrelated_standing_unreached() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    let first = ecology
        .receive(&informant("A", 10, &["x", "y"]), action())
        .unwrap();
    assert_eq!(first.regional().touched_constituents(), 0);
    let unrelated = ecology
        .receive(&informant("U", 20, &["u", "v"]), action())
        .unwrap();
    assert_eq!(unrelated.regional().touched_constituents(), 0);
    let second = ecology
        .receive(&informant("B", 30, &["y", "z"]), action())
        .unwrap();
    assert_eq!(second.regional().touched_constituents(), 1);
    assert_eq!(second.regional().front_depth(), 1);
    assert_eq!(ecology.machine().standing().constituents().len(), 2);

    let rest = ecology.rest_image().unwrap();
    let rest_bytes = rest.encode_native_bytes().unwrap();
    let reopened_image = ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).unwrap();
    assert_eq!(reopened_image, rest);
    let mut probe = ResonanceEcology::from_rest_image(reopened_image).unwrap();
    let result = probe
        .receive(
            &ResonanceOccurrence::probe(40, vec![germ("x")]).unwrap(),
            action(),
        )
        .unwrap();
    assert_eq!(result.regional().touched_constituents(), 1);
    assert_eq!(result.regional().front_depth(), 1);
    assert_eq!(result.read().informants().len(), 2);
    assert!(result
        .read()
        .germs()
        .contains(&fiber_from_bytes(TEST_SCHEMA, b"z")));
    assert!(!result
        .read()
        .germs()
        .contains(&fiber_from_bytes(TEST_SCHEMA, b"u")));

    let reopened = ResonanceEcology::from_rest_image(rest).unwrap();
    assert_eq!(reopened.machine().standing(), ecology.machine().standing());
}

#[test]
fn conditioned_ecology_wire_refuses_partial_or_changed_structure() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    ecology
        .receive(&informant("A", 10, &["x", "y"]), action())
        .unwrap();
    let wire = ecology.rest_image().unwrap().encode_native_bytes().unwrap();

    assert!(ResonanceEcologyRestImage::from_native_bytes(&wire[..wire.len() - 1]).is_err());
    let mut changed = wire;
    changed[0] ^= 1;
    assert!(ResonanceEcologyRestImage::from_native_bytes(&changed).is_err());
}

#[test]
fn sequential_reception_retains_history_but_returns_one_resonant_quotient() {
    let train = |events: [ResonanceOccurrence; 3]| {
        let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
        let mut ecology = ResonanceEcology::new(machine);
        for event in events {
            ecology.receive(&event, action()).unwrap();
        }
        ecology
    };
    let forward = train([
        informant("A", 10, &["x", "y"]),
        informant("B", 20, &["y", "z"]),
        informant("U", 30, &["u", "v"]),
    ]);
    let reverse = train([
        informant("U", 30, &["u", "v"]),
        informant("B", 20, &["y", "z"]),
        informant("A", 10, &["x", "y"]),
    ]);
    // Training chronology remains real lineage: reversing physical delivery must not erase
    // the two histories into one standing wire.
    assert_ne!(forward.machine().standing(), reverse.machine().standing());

    // The conditioned association is nevertheless chronology-gauge. The same receiver
    // question crosses the same semantic component and returns the same structural image.
    let question = ResonanceOccurrence::probe(40, vec![germ("x")]).unwrap();
    let mut forward_probe =
        ResonanceEcology::from_rest_image(forward.rest_image().unwrap()).unwrap();
    let mut reverse_probe =
        ResonanceEcology::from_rest_image(reverse.rest_image().unwrap()).unwrap();
    let forward_return = forward_probe.receive(&question, action()).unwrap();
    let reverse_return = reverse_probe.receive(&question, action()).unwrap();
    assert_eq!(forward_return.read(), reverse_return.read());
    assert_eq!(
        forward_return.regional().touched_constituents(),
        reverse_return.regional().touched_constituents()
    );
    assert_eq!(
        forward_return.regional().front_depth(),
        reverse_return.regional().front_depth()
    );
}

#[test]
fn one_independent_configuration_is_exactly_delivery_order_gauge() {
    let train = |schedule: [usize; 3]| {
        let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
        let mut ecology = ResonanceEcology::new(machine);
        let configuration = schedule.map(|at| match at {
            0 => informant("A", 10, &["x", "y"]),
            1 => informant("B", 20, &["y", "z"]),
            2 => informant("U", 30, &["u", "v"]),
            _ => unreachable!("the schedule contains only the three declared informants"),
        });
        ecology
            .receive_configuration(&configuration, action())
            .unwrap();
        ecology
    };
    let forward = train([0, 1, 2]);
    let reverse = train([2, 1, 0]);
    assert_eq!(forward.machine().standing(), reverse.machine().standing());
    assert_eq!(
        forward.machine().rest_image().unwrap(),
        reverse.machine().rest_image().unwrap()
    );
}

#[test]
fn same_identity_with_changed_phase_remains_an_open_residual() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    ecology
        .receive(&informant("A", 10, &["x"]), action())
        .unwrap();
    let changed = ResonanceGerm::new(
        fiber_from_bytes(TEST_SCHEMA, b"x"),
        RelationAtom::new(Cog::lit(11)).unwrap(),
    );
    let result = ecology
        .receive(
            &ResonanceOccurrence::informant(
                fiber_from_bytes(INFORMANT_SCHEMA, b"B"),
                20,
                vec![changed],
            )
            .unwrap(),
            action(),
        )
        .unwrap();
    assert_eq!(result.regional().touched_constituents(), 1);
    assert!(result
        .regional()
        .support_transitions()
        .iter()
        .flatten()
        .any(|transition| *transition == LiveBoundaryTransition::Open));
    assert!(result
        .read()
        .interfaces()
        .iter()
        .any(|witness| witness.conduct() == ResonancePinConduct::Open));
}

#[test]
fn complete_recurrence_closes_a_ride() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    ecology
        .receive(&informant("A", 10, &["x", "y"]), action())
        .unwrap();
    let result = ecology
        .receive(&informant("A", 30, &["x", "y"]), action())
        .unwrap();
    assert!(result
        .regional()
        .support_transitions()
        .iter()
        .flatten()
        .any(|transition| *transition == LiveBoundaryTransition::Ride));
    assert!(result
        .read()
        .interfaces()
        .iter()
        .any(|witness| witness.conduct() == ResonancePinConduct::Riding));
}

#[test]
fn unrelated_riding_port_cannot_complete_the_declared_open_port() {
    let open_germ = || {
        ResonanceGerm::new(
            fiber_from_bytes(TEST_SCHEMA, b"open-port"),
            RelationAtom::new(Cog::lit(1)).unwrap(),
        )
    };
    let riding_germ = || {
        ResonanceGerm::new(
            fiber_from_bytes(TEST_SCHEMA, b"riding-port"),
            RelationAtom::new(Cog::lit(2)).unwrap(),
        )
    };
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    ecology
        .receive(
            &ResonanceOccurrence::informant(
                fiber_from_bytes(INFORMANT_SCHEMA, b"first"),
                10,
                vec![open_germ(), riding_germ()],
            )
            .unwrap(),
            action(),
        )
        .unwrap();
    let returned = ecology
        .receive_configuration(
            &[ResonanceOccurrence::informant(
                fiber_from_bytes(INFORMANT_SCHEMA, b"second"),
                20,
                vec![open_germ(), riding_germ()],
            )
            .unwrap()
            .with_required_germ_ports(LocalSet::from([fiber_from_bytes(
                TEST_SCHEMA,
                b"open-port",
            )]))
            .unwrap()],
            action(),
        )
        .unwrap();
    let read = &returned.reads()[0];
    assert!(read.constituent().interfaces().iter().any(|witness| {
        witness.antecedent() == riding_germ().identity()
            && witness.conduct() == ResonancePinConduct::Riding
    }));
    assert!(matches!(
        read.conduct(),
        ResonanceOccurrenceConduct::Open { .. }
    ));
    assert_eq!(
        read.conduct().required(),
        &LocalSet::from([ResonancePinPort::new(
            fiber_from_bytes(TEST_SCHEMA, b"open-port"),
            role_fiber(GERM_ROLE_WORD),
        )])
    );
}

#[test]
fn conduct_aperture_rejects_empty_and_foreign_germ_ports() {
    assert_eq!(
        informant("A", 10, &["x", "y"])
            .with_required_germ_ports(LocalSet::new())
            .unwrap_err(),
        ResonanceEcologyError::MalformedRadiation
    );
    assert_eq!(
        informant("A", 10, &["x", "y"])
            .with_required_germ_ports(LocalSet::from([fiber_from_bytes(TEST_SCHEMA, b"foreign",)]))
            .unwrap_err(),
        ResonanceEcologyError::MalformedRadiation
    );
}

#[test]
fn continuation_question_emanates_a_plural_family_without_a_supplied_target() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    let inherited = [
        ResonanceOccurrence::continuation_informant(
            fiber_from_bytes(INFORMANT_SCHEMA, b"A"),
            10,
            ["a", "b", "c"].map(germ).to_vec(),
        )
        .unwrap(),
        ResonanceOccurrence::continuation_informant(
            fiber_from_bytes(INFORMANT_SCHEMA, b"B"),
            20,
            ["a", "d", "e"].map(germ).to_vec(),
        )
        .unwrap(),
    ];
    ecology.receive_configuration(&inherited, action()).unwrap();
    let trained = ecology.rest_image().unwrap();

    let question = ResonanceOccurrence::continuation_probe(30, vec![germ("a")]).unwrap();
    let emanation = ecology.receive_and_emanate(&question, action()).unwrap();
    let expected_b = fiber_from_bytes(TEST_SCHEMA, b"b");
    let expected_d = fiber_from_bytes(TEST_SCHEMA, b"d");
    assert_eq!(emanation.branches().len(), 2);
    assert!(emanation
        .branches()
        .iter()
        .any(|branch| branch.germ().identity() == &expected_b));
    assert!(emanation
        .branches()
        .iter()
        .any(|branch| branch.germ().identity() == &expected_d));
    assert!(emanation
        .radiation()
        .read()
        .origins()
        .contains(&ResonanceOccurrenceOrigin::Inherited));
    assert!(emanation
        .radiation()
        .read()
        .origins()
        .contains(&ResonanceOccurrenceOrigin::ReceiverQuestion));

    let branch = emanation.branch_occurrence(0, 40).unwrap();
    assert_eq!(branch.origin(), ResonanceOccurrenceOrigin::SelfEmanated);
    let mut enacted = ResonanceEcology::from_rest_image(trained).unwrap();
    let returned = enacted.receive(&branch, action()).unwrap();
    assert!(returned
        .read()
        .origins()
        .contains(&ResonanceOccurrenceOrigin::SelfEmanated));
    assert!(returned
        .read()
        .origins()
        .contains(&ResonanceOccurrenceOrigin::Inherited));
}

#[test]
fn ordered_paths_retain_repeated_germ_occurrences() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = ResonanceEcology::new(machine);
    let repeated = ResonanceOccurrence::continuation_informant(
        fiber_from_bytes(INFORMANT_SCHEMA, b"ABA"),
        10,
        ["a", "b", "a"].map(germ).to_vec(),
    )
    .unwrap();
    ecology.receive(&repeated, action()).unwrap();

    let question = ResonanceOccurrence::continuation_probe(20, vec![germ("b")]).unwrap();
    let emanation = ecology.receive_and_emanate(&question, action()).unwrap();
    assert_eq!(emanation.branches().len(), 1);
    assert_eq!(
        emanation.branches()[0].germ().identity(),
        germ("a").identity()
    );
}
