use super::*;
use crate::{
    BoundaryId, ExactUnitConicPhase, OccurrencePort,
    native_ecology::holonic_intelligence::{
        CarrierRank, CycleRank, DimensionFace, DimensionObstruction, DismantlingBoundaryReturn,
        ForeignConfigurationChart, IncidenceNullity, IncidenceRank, NativeTransportRequest,
        RestedTransportEcology, profile_dismantling_return,
    },
};
use num_bigint::BigInt;
use relational_geometry::Rat;

fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(
        Rat::from_integer(BigInt::from(real)),
        Rat::from_integer(BigInt::from(imaginary)),
    )
}

fn thread(
    address: &str,
    event: u64,
    entering_boundary: u64,
    emitting_boundary: u64,
    from: u64,
    to: u64,
    generator: u64,
) -> NativeThread {
    let occurrence = EventId(event);
    let from = NativeStateId(from);
    let to = NativeStateId(to);
    let receiver = ReceiverId(9);
    NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: address.to_owned(),
        entering_boundary: BoundaryId(entering_boundary),
        emitting_boundary: BoundaryId(emitting_boundary),
        entering_carrier: "native-complex-section".to_owned(),
        emitting_carrier: "native-complex-section".to_owned(),
        occurrences: vec![NativeThreadOccurrence {
            occurrence,
            predecessor: None,
            entering_port: OccurrencePort::input(occurrence, 0),
            emitting_port: OccurrencePort::output(occurrence, 0),
            entering_native: from,
            emitting_native: to,
        }],
        native_support: BTreeSet::from([from, to]),
        incidence: vec![NativeIncidenceTerm {
            occurrence,
            from,
            to,
            coefficient: 1,
        }],
        parametrons: vec![
            NativeParametronCell {
                native: from,
                section: current(1, 0),
                current: current(0, 1),
                relative_phase: ExactUnitConicPhase::identity(),
                hand: NativeThreadHand::Along,
            },
            NativeParametronCell {
                native: to,
                section: current(0, 1),
                current: current(-1, 0),
                relative_phase: ExactUnitConicPhase::identity(),
                hand: NativeThreadHand::Along,
            },
        ],
        constitutive_responses: vec![
            NativeConstitutiveResponse {
                native: from,
                receiver,
                presented: current(1, 0),
                stored: current(0, 1),
            },
            NativeConstitutiveResponse {
                native: to,
                receiver,
                presented: current(0, 1),
                stored: current(-1, 0),
            },
        ],
        chronology: vec![InputId(generator)],
        receiver_consequences: vec![
            NativeReceiverConsequence {
                native: from,
                receiver,
                observation: Observation(from.0 + 100),
            },
            NativeReceiverConsequence {
                native: to,
                receiver,
                observation: Observation(to.0 + 100),
            },
        ],
        obstruction: None,
        open_exterior: vec!["receiver/history outside the admitted family".to_owned()],
        reconstruction_fibre: BTreeSet::from([occurrence]),
    }
}

fn spool() -> NativeSpool {
    let left = thread("thread/turn-out", 1, 10, 11, 0, 1, 7);
    let right = thread("thread/turn-back", 2, 11, 10, 1, 0, 7);
    NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "spool/native-turn".to_owned(),
        native_population: BTreeSet::from([NativeStateId(0), NativeStateId(1)]),
        receiver_family: BTreeSet::from([ReceiverId(9)]),
        generator_family: BTreeSet::from([InputId(7)]),
        threads: vec![left, right],
        serial_pullbacks: vec![
            NativeSerialPullback {
                left_thread: "thread/turn-out".to_owned(),
                right_thread: "thread/turn-back".to_owned(),
                joining_boundary: BoundaryId(11),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: EventId(1),
                    right: EventId(2),
                    joining_native: NativeStateId(1),
                }]),
            },
            NativeSerialPullback {
                left_thread: "thread/turn-back".to_owned(),
                right_thread: "thread/turn-out".to_owned(),
                joining_boundary: BoundaryId(10),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: EventId(2),
                    right: EventId(1),
                    joining_native: NativeStateId(0),
                }]),
            },
        ],
        generator_descents: vec![NativeGeneratorDescent {
            generator: InputId(7),
            steps: vec![
                NativeGeneratorStep {
                    from: NativeStateId(0),
                    to: NativeStateId(1),
                    thread: "thread/turn-out".to_owned(),
                },
                NativeGeneratorStep {
                    from: NativeStateId(1),
                    to: NativeStateId(0),
                    thread: "thread/turn-back".to_owned(),
                },
            ],
            open_domain: BTreeSet::new(),
        }],
        receiver_factors: vec![
            ReceiverFactor {
                native: NativeStateId(0),
                receiver: ReceiverId(9),
                observation: Observation(100),
            },
            ReceiverFactor {
                native: NativeStateId(1),
                receiver: ReceiverId(9),
                observation: Observation(101),
            },
        ],
        mutual_constitutive_responses: Vec::new(),
        reconstruction_fibres: vec![
            NativeCollapsedFibre {
                native: NativeStateId(0),
                occurrences: BTreeSet::from([EventId(2)]),
            },
            NativeCollapsedFibre {
                native: NativeStateId(1),
                occurrences: BTreeSet::from([EventId(1)]),
            },
        ],
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["larger receiver family".to_owned()],
    }
}

fn scaffold() -> NativeTransportScaffold {
    NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: "scaffold/native-turn".to_owned(),
        spools: vec![spool()],
        compositions: Vec::new(),
        open_exterior: vec!["another compatible spool".to_owned()],
    }
}

fn ordered_consequence(
    order: Vec<String>,
    successor: NativeStateId,
    lineage_occurrences: BTreeSet<EventId>,
) -> NativeOrderedConsequence {
    NativeOrderedConsequence {
        order,
        successor,
        obstructions: BTreeSet::new(),
        lineage_occurrences,
        logical_resources: BTreeMap::new(),
    }
}

fn thread_deposit() -> NativeThreadDeposit {
    let mut deposited_thread = thread("thread/cultivated-return", 3, 10, 11, 0, 1, 7);
    deposited_thread.occurrences[0].predecessor = Some(EventId(2));
    let candidate_left = current(1, 0);
    let candidate_right = current(1, 0);
    let returned_left = current(2, 0);
    let returned_right = current(3, 0);
    let left_difference = returned_left.subtract(&candidate_left);
    let right_difference = returned_right.subtract(&candidate_right);
    let storage = Rat::from_integer(BigInt::from(1));
    let candidate_product = candidate_left.multiply(&candidate_right).scaled(&storage);
    let source_linear_terms = candidate_left
        .multiply(&right_difference)
        .add(&left_difference.multiply(&candidate_right))
        .scaled(&storage);
    let mixed_remainder = left_difference.multiply(&right_difference).scaled(&storage);
    let reconstructed_returned_product = candidate_product
        .add(&source_linear_terms)
        .add(&mixed_remainder);
    let returned_product = returned_left.multiply(&returned_right).scaled(&storage);
    let lineage = BTreeSet::from([EventId(1), EventId(3)]);
    NativeThreadDeposit {
        schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
        spool_address: "spool/native-turn".to_owned(),
        thread: deposited_thread,
        serial_pullbacks: vec![
            NativeSerialPullback {
                left_thread: "thread/turn-back".to_owned(),
                right_thread: "thread/cultivated-return".to_owned(),
                joining_boundary: BoundaryId(10),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: EventId(2),
                    right: EventId(3),
                    joining_native: NativeStateId(0),
                }]),
            },
            NativeSerialPullback {
                left_thread: "thread/cultivated-return".to_owned(),
                right_thread: "thread/turn-back".to_owned(),
                joining_boundary: BoundaryId(11),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: EventId(3),
                    right: EventId(2),
                    joining_native: NativeStateId(1),
                }]),
            },
        ],
        generator_descents: Vec::new(),
        receiver_factors: Vec::new(),
        mutual_constitutive_responses: vec![NativeMutualConstitutiveResponse {
            left_occurrence: EventId(1),
            right_occurrence: EventId(3),
            left_native: NativeStateId(0),
            right_native: NativeStateId(0),
            receiver: ReceiverId(9),
            storage: Rat::from_integer(BigInt::from(1)),
        }],
        mixed_constitutive_families: vec![NativeMixedConstitutiveFamily {
            address: "mixed/turn-out/cultivated-return".to_owned(),
            left_thread: "thread/turn-out".to_owned(),
            right_thread: "thread/cultivated-return".to_owned(),
            receiver: ReceiverId(9),
            storage,
            candidate_left,
            candidate_right,
            returned_left,
            returned_right,
            left_difference,
            right_difference,
            candidate_product,
            source_linear_terms,
            mixed_remainder,
            reconstructed_returned_product,
            returned_product,
            dependent_receiver_support: BTreeSet::from([NativeStateId(100), NativeStateId(101)]),
            pair_population: 1,
        }],
        shortest_separators: vec![NativeShortestSeparator {
            left: EventId(1),
            right: EventId(3),
            word: vec![InputId(7)],
            receiver: ReceiverId(9),
            left_observation: Observation(1),
            right_observation: Observation(2),
        }],
        interchanges: vec![NativeInterchangeReceipt {
            left_thread: "thread/turn-out".to_owned(),
            right_thread: "thread/cultivated-return".to_owned(),
            left_then_right: ordered_consequence(
                vec![
                    "thread/turn-out".to_owned(),
                    "thread/cultivated-return".to_owned(),
                ],
                NativeStateId(1),
                lineage.clone(),
            ),
            right_then_left: ordered_consequence(
                vec![
                    "thread/cultivated-return".to_owned(),
                    "thread/turn-out".to_owned(),
                ],
                NativeStateId(1),
                lineage,
            ),
        }],
        reconstruction_fibre_deltas: vec![NativeDepositFibreDelta {
            native: NativeStateId(1),
            occurrences: BTreeSet::from([EventId(3)]),
        }],
        exact_reconstruction_fibres: vec![NativeExactReconstructionFibre {
            address: "fibre/candidate-return/2-3".to_owned(),
            thread: "thread/cultivated-return".to_owned(),
            return_operator: ExactRatMatrix::identity(1).expect("identity"),
            terminal_covector: vec![Rat::from_integer(BigInt::from(5))],
            returned_covector: vec![Rat::from_integer(BigInt::from(5))],
            particular: vec![Rat::from_integer(BigInt::from(5))],
            radical: Vec::new(),
            obstruction: None,
            carrying_pullback: NativePullbackOccurrence {
                left: EventId(2),
                right: EventId(3),
                joining_native: NativeStateId(0),
            },
            k3_native_support: BTreeSet::from([NativeStateId(0), NativeStateId(1)]),
            dependent_receiver_fibre: BTreeSet::from([NativeStateId(100), NativeStateId(101)]),
            occurrences: BTreeSet::from([EventId(2), EventId(3)]),
            open_exterior: vec!["richer successor receiver".to_owned()],
        }],
    }
}

fn thread_deposit_at(address: &str, event: u64) -> NativeThreadDeposit {
    let mut deposit = thread_deposit();
    let event = EventId(event);
    deposit.thread.address = address.to_owned();
    deposit.thread.occurrences[0].occurrence = event;
    deposit.thread.occurrences[0].entering_port = OccurrencePort::input(event, 0);
    deposit.thread.occurrences[0].emitting_port = OccurrencePort::output(event, 0);
    deposit.thread.incidence[0].occurrence = event;
    deposit.thread.reconstruction_fibre = BTreeSet::from([event]);
    deposit.serial_pullbacks[0].right_thread = address.to_owned();
    deposit.serial_pullbacks[0].occurrences = BTreeSet::from([NativePullbackOccurrence {
        left: EventId(2),
        right: event,
        joining_native: NativeStateId(0),
    }]);
    deposit.serial_pullbacks[1].left_thread = address.to_owned();
    deposit.serial_pullbacks[1].occurrences = BTreeSet::from([NativePullbackOccurrence {
        left: event,
        right: EventId(2),
        joining_native: NativeStateId(1),
    }]);
    deposit.mutual_constitutive_responses[0].right_occurrence = event;
    deposit.shortest_separators[0].right = event;
    deposit.interchanges[0].right_thread = address.to_owned();
    deposit.interchanges[0].left_then_right.order[1] = address.to_owned();
    deposit.interchanges[0].right_then_left.order[0] = address.to_owned();
    let lineage = BTreeSet::from([EventId(1), event]);
    deposit.interchanges[0].left_then_right.lineage_occurrences = lineage.clone();
    deposit.interchanges[0].right_then_left.lineage_occurrences = lineage;
    deposit.reconstruction_fibre_deltas[0].occurrences = BTreeSet::from([event]);
    deposit.exact_reconstruction_fibres[0].address = format!("fibre/2-{}", event.0);
    deposit.exact_reconstruction_fibres[0].thread = address.to_owned();
    deposit.exact_reconstruction_fibres[0]
        .carrying_pullback
        .right = event;
    deposit.exact_reconstruction_fibres[0].occurrences = BTreeSet::from([EventId(2), event]);
    deposit.mixed_constitutive_families.clear();
    deposit
}

fn mixed_family(
    address: &str,
    left_thread: &str,
    right_thread: &str,
) -> NativeMixedConstitutiveFamily {
    let mut family = thread_deposit().mixed_constitutive_families.remove(0);
    family.address = address.to_owned();
    family.left_thread = left_thread.to_owned();
    family.right_thread = right_thread.to_owned();
    family
}

fn rank_four_deposit_batch() -> Vec<NativeThreadDeposit> {
    let addresses = [
        "thread/cycle-a",
        "thread/cycle-b",
        "thread/cycle-c",
        "thread/cycle-d",
    ];
    let mut deposits = addresses
        .iter()
        .enumerate()
        .map(|(at, address)| thread_deposit_at(address, 3 + at as u64))
        .collect::<Vec<_>>();
    for left in 0..addresses.len() {
        for right in left..addresses.len() {
            deposits[left]
                .mixed_constitutive_families
                .push(mixed_family(
                    &format!("mixed/{left}/{right}"),
                    addresses[left],
                    addresses[right],
                ));
        }
    }
    deposits.reverse();
    deposits
}

#[test]
fn native_scaffold_round_trips_without_ancestry_fields() {
    let scaffold = scaffold();
    let bytes = scaffold.canonical_bytes().expect("valid scaffold");
    let remounted = NativeTransportScaffold::read(&bytes).expect("remount");
    assert_eq!(remounted, scaffold);
    let text = String::from_utf8(bytes).expect("json").to_ascii_lowercase();
    for forbidden in [
        "soulkiller",
        "phoenix",
        "foreign",
        "model_name",
        "tensor",
        "token_id",
        "source_executor",
        "q_proj",
        "k_proj",
        "v_proj",
    ] {
        assert!(
            !text.contains(forbidden),
            "native wire contains {forbidden}"
        );
    }
}

#[test]
fn situated_deposit_withdrawal_and_redeposit_prove_both_identity_compositions() {
    let predecessor = scaffold();
    let predecessor_identity = native_scaffold_identity(&predecessor).expect("predecessor");
    let deposit = thread_deposit();
    let deposit_identity = native_deposit_identity(&deposit).expect("deposit");
    let (situated, receipt) = predecessor.deposit_thread(deposit).expect("atomic deposit");
    let successor_identity = situated.identity_sha256().expect("successor");
    assert_eq!(receipt.predecessor_identity_sha256, predecessor_identity);
    assert_eq!(receipt.successor_identity_sha256, successor_identity);
    assert_eq!(receipt.deposit_identity_sha256, deposit_identity);
    assert_eq!(situated.mixed_constitutive_families().len(), 1);
    assert_eq!(situated.exact_reconstruction_fibres().len(), 1);
    assert_eq!(situated.mixed_constitutive_families()[0].pair_population, 1);

    let (predecessor, recovered) = situated
        .withdraw_deposit(receipt.clone())
        .expect("exact inverse");
    assert_eq!(
        predecessor.identity_sha256().expect("recovered identity"),
        predecessor_identity
    );
    assert_eq!(
        native_deposit_identity(&recovered).expect("recovered deposit"),
        deposit_identity
    );
    let SituatedNativeTransportPredecessor::Native(predecessor) = predecessor else {
        panic!("first withdrawal must return the admitted native predecessor")
    };
    let (redeposited, second_receipt) = predecessor
        .deposit_thread(recovered)
        .expect("exact redeposit");
    assert_eq!(
        redeposited.identity_sha256().expect("redeposit"),
        successor_identity
    );
    assert_eq!(second_receipt, receipt);
}

#[test]
fn rank_four_batch_is_one_symmetric_body_and_round_trips_without_intermediate_rest() {
    let predecessor = scaffold();
    let predecessor_identity = native_scaffold_identity(&predecessor).expect("predecessor");
    let deposits = rank_four_deposit_batch();
    let (situated, receipt) = predecessor
        .deposit_threads(deposits)
        .expect("one atomic rank-four deposit");
    assert_eq!(receipt.symmetric_constitutive_body.diagonal_population, 4);
    assert_eq!(
        receipt.symmetric_constitutive_body.distinct_pair_population,
        6
    );
    assert_eq!(receipt.symmetric_constitutive_body.symmetric_population, 10);
    assert_eq!(receipt.symmetric_constitutive_body.terms.len(), 10);
    assert_eq!(receipt.placements.len(), 4);
    assert_eq!(situated.mixed_constitutive_families().len(), 10);
    let successor_identity = situated.identity_sha256().expect("successor");

    let (predecessor, recovered) = situated
        .withdraw_deposit_batch(receipt.clone())
        .expect("complete batch inverse");
    assert_eq!(
        native_scaffold_identity(&predecessor).expect("recovered predecessor"),
        predecessor_identity
    );
    assert_eq!(recovered.len(), 4);
    let (redeposited, redeposit_receipt) = predecessor
        .deposit_threads(recovered)
        .expect("one atomic redeposit");
    assert_eq!(
        redeposited.identity_sha256().expect("redeposited"),
        successor_identity
    );
    assert_eq!(redeposit_receipt, receipt);
}

#[test]
fn rank_four_batch_refuses_the_alternating_six_as_a_symmetric_square() {
    let mut deposits = rank_four_deposit_batch();
    let owner = deposits
        .iter_mut()
        .find(|deposit| deposit.thread.address == "thread/cycle-a")
        .expect("canonical owner");
    owner
        .mixed_constitutive_families
        .retain(|family| family.left_thread != family.right_thread);
    assert!(matches!(
        scaffold().deposit_threads(deposits),
        Err(NativeSpoolRefusal::ThreadDepositBatchReceipt)
    ));
}

#[test]
fn arbitrary_situated_withdrawal_moves_every_incident_relation_and_restores() {
    let (situated, _) = scaffold()
        .deposit_thread(thread_deposit())
        .expect("atomic deposit");
    let identity = situated.identity_sha256().expect("identity");
    let (ablated, withdrawal) = situated
        .withdraw_thread("spool/native-turn", "thread/cultivated-return")
        .expect("targeted withdrawal");
    assert!(ablated.mixed_constitutive_families().is_empty());
    assert!(ablated.exact_reconstruction_fibres().is_empty());
    assert_eq!(withdrawal.mixed_constitutive_families.len(), 1);
    assert_eq!(withdrawal.exact_reconstruction_fibres.len(), 1);
    let restored = ablated.restore_thread(withdrawal).expect("restore");
    assert_eq!(restored.identity_sha256().expect("restored"), identity);
}

#[test]
fn receiver_radical_withdrawal_changes_the_fibre_and_restores_exact_identity() {
    let mut deposit = thread_deposit();
    let fibre = &mut deposit.exact_reconstruction_fibres[0];
    fibre.return_operator = ExactRatMatrix::new(vec![vec![
        Rat::from_integer(BigInt::from(1)),
        Rat::from_integer(BigInt::from(0)),
    ]])
    .expect("one-dimensional returned receiver over a two-dimensional domain");
    fibre.terminal_covector = vec![
        Rat::from_integer(BigInt::from(5)),
        Rat::from_integer(BigInt::from(7)),
    ];
    fibre.returned_covector = vec![Rat::from_integer(BigInt::from(5))];
    fibre.particular = vec![
        Rat::from_integer(BigInt::from(5)),
        Rat::from_integer(BigInt::from(0)),
    ];
    fibre.radical = vec![vec![
        Rat::from_integer(BigInt::from(0)),
        Rat::from_integer(BigInt::from(1)),
    ]];
    fibre
        .validate()
        .expect("the enlarged exact fibre is lawful");

    let (situated, _) = scaffold().deposit_thread(deposit).expect("atomic deposit");
    let identity = situated.identity_sha256().expect("identity");
    let fibre_address = situated.exact_reconstruction_fibres()[0].address.clone();
    let returned_before = situated.exact_reconstruction_fibres()[0]
        .returned_covector
        .clone();
    let (ablated, withdrawal) = situated
        .withdraw_radical_direction(&fibre_address, 0)
        .expect("kernel direction moves out of the reconstruction body");
    assert!(ablated.exact_reconstruction_fibres()[0].radical.is_empty());
    assert_eq!(
        ablated.exact_reconstruction_fibres()[0].returned_covector,
        returned_before
    );
    assert_ne!(
        ablated.identity_sha256().expect("ablated identity"),
        identity
    );

    let restored = ablated
        .restore_radical_direction(withdrawal)
        .expect("kernel direction restores");
    assert_eq!(restored.identity_sha256().expect("restored"), identity);
}

#[test]
fn mixed_remainder_and_actual_carrying_pullback_are_firing_falsifiers() {
    let mut deposit = thread_deposit();
    deposit.mixed_constitutive_families[0].mixed_remainder = current(0, 0);
    assert!(matches!(
        scaffold().deposit_thread(deposit),
        Err(NativeSpoolRefusal::MixedConstitutiveFamily(_))
    ));

    let mut deposit = thread_deposit();
    deposit.exact_reconstruction_fibres[0]
        .carrying_pullback
        .left = EventId(1);
    assert!(matches!(
        scaffold().deposit_thread(deposit),
        Err(NativeSpoolRefusal::ExactReconstructionFibre(_))
    ));
}

#[test]
fn native_addressed_section_borrows_the_exact_occurrence_carrier() {
    let scaffold = scaffold();
    let section = scaffold
        .addressed_section("spool/native-turn", "thread/turn-out", EventId(1))
        .expect("addressed section");

    section.validate().expect("validated borrowed view");
    assert_eq!(section.scaffold_address(), "scaffold/native-turn");
    assert_eq!(section.spool().address, "spool/native-turn");
    assert_eq!(section.thread().address, "thread/turn-out");
    assert_eq!(section.occurrence().occurrence, EventId(1));
    assert_eq!(section.incidence().coefficient, 1);
    assert_eq!(section.entering_parametron().native, NativeStateId(0));
    assert_eq!(section.emitting_parametron().native, NativeStateId(1));
    assert_eq!(section.ordered_generator_word(), &[InputId(7)]);
    assert_eq!(
        section.reconstruction_fibre().occurrences,
        BTreeSet::from([EventId(1)])
    );
}

#[test]
fn native_addressed_section_returns_exact_unsupported_families() {
    let scaffold = scaffold();
    let section = scaffold
        .addressed_section("spool/native-turn", "thread/turn-out", EventId(1))
        .expect("addressed section");

    let receiver = ReceiverInsufficiency::receiver_outside_family(
        &section,
        ReceiverId(10),
        vec!["receiver 10 remains outside the admitted family".to_owned()],
    )
    .expect("receiver insufficiency");
    assert_eq!(receiver.at_occurrence, EventId(1));
    assert_eq!(receiver.native, NativeStateId(1));
    assert_eq!(receiver.retained_fibre, BTreeSet::from([EventId(1)]));
    assert!(matches!(
        receiver.cause,
        ReceiverInsufficiencyCause::ReceiverOutsideFamily { requested, admitted }
            if requested == ReceiverId(10)
                && admitted == BTreeSet::from([ReceiverId(9)])
    ));

    let word = ReceiverInsufficiency::successor_word_outside_family(
        &section,
        vec![InputId(7), InputId(8)],
        vec!["generator 8 remains outside the admitted family".to_owned()],
    )
    .expect("successor insufficiency");
    assert!(matches!(
        word.cause,
        ReceiverInsufficiencyCause::SuccessorOutsideFamily {
            requested_word,
            admitted_generators,
        } if requested_word == vec![InputId(7), InputId(8)]
            && admitted_generators == BTreeSet::from([InputId(7)])
    ));

    let absent = ReceiverInsufficiency::section_outside_family(
        &section,
        EventId(3),
        vec!["occurrence 3 remains outside the admitted section family".to_owned()],
    )
    .expect("section insufficiency");
    assert!(matches!(
        absent.cause,
        ReceiverInsufficiencyCause::SectionOutsideFamily { requested, admitted }
            if requested == EventId(3)
                && admitted == BTreeSet::from([EventId(1), EventId(2)])
    ));

    assert!(matches!(
        ReceiverInsufficiency::receiver_outside_family(
            &section,
            ReceiverId(9),
            vec!["not actually outside".to_owned()],
        ),
        Err(NativeSpoolRefusal::Insufficiency)
    ));
    assert!(matches!(
        ReceiverInsufficiency::successor_word_outside_family(
            &section,
            vec![InputId(7)],
            vec!["not actually outside".to_owned()],
        ),
        Err(NativeSpoolRefusal::Insufficiency)
    ));
    assert!(matches!(
        ReceiverInsufficiency::section_outside_family(
            &section,
            EventId(2),
            vec!["not actually outside".to_owned()],
        ),
        Err(NativeSpoolRefusal::Insufficiency)
    ));
}

#[test]
fn serial_receipt_must_retain_the_complete_pullback_population() {
    let mut spool = spool();
    spool.serial_pullbacks[0].occurrences.clear();
    assert!(matches!(
        spool.validate(),
        Err(NativeSpoolRefusal::Pullback(_, _))
    ));
}

#[test]
fn an_unobstructed_all_zero_thread_is_not_productive() {
    let mut thread = thread("thread/zero", 4, 20, 21, 0, 1, 7);
    for cell in &mut thread.parametrons {
        cell.section = ExactComplexWaveCurrent::zero();
        cell.current = ExactComplexWaveCurrent::zero();
    }
    assert!(matches!(
        thread.validate(),
        Err(NativeSpoolRefusal::Parametron(_))
    ));
}

#[test]
fn insufficiency_exhibits_the_reopened_native_fibre() {
    let insufficiency = ReceiverInsufficiency {
        schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
        at_occurrence: EventId(8),
        native: NativeStateId(3),
        retained_fibre: BTreeSet::from([EventId(8), EventId(9)]),
        cause: ReceiverInsufficiencyCause::ReconstructionFibreReopened {
            separator: NativeShortestSeparator {
                left: EventId(8),
                right: EventId(9),
                word: vec![InputId(4)],
                receiver: ReceiverId(11),
                left_observation: Observation(1),
                right_observation: Observation(2),
            },
        },
        open_exterior: vec!["successor outside the admitted section".to_owned()],
    };
    insufficiency.validate().expect("exact insufficiency");
}

#[test]
fn intrinsic_profile_borrows_every_native_facet_and_keeps_dimensions_typed() {
    let scaffold = scaffold();
    let profile = scaffold
        .intrinsic_holon_profile()
        .expect("intrinsic profile");
    assert_eq!(profile.scaffold_address, scaffold.address);
    assert_eq!(profile.holons.len(), 2);
    assert!(std::ptr::eq(
        profile.holons[0].morphology,
        &scaffold.spools[0].threads[0]
    ));
    let holon = &profile.holons[0];
    assert_eq!(
        holon.dimensions.incidence_rank,
        DimensionFace::Exact(IncidenceRank(1))
    );
    assert_eq!(
        holon.dimensions.incidence_nullity,
        DimensionFace::Exact(IncidenceNullity(0))
    );
    assert_eq!(
        holon.dimensions.cycle_rank,
        DimensionFace::Exact(CycleRank(0))
    );
    assert_eq!(
        holon.dimensions.carrier_rank,
        DimensionFace::Exact(CarrierRank(2))
    );
    assert_eq!(
        holon.dimensions.scale_extent,
        DimensionFace::Open(DimensionObstruction::ScaleChartOutsideNativeThread)
    );
    assert_eq!(holon.incidence.terms.len(), 1);
    assert_eq!(holon.carrier.parametrons.len(), 2);
    assert_eq!(holon.transport.generator_descents.len(), 1);
    assert_eq!(holon.transport.serial_pullbacks.len(), 2);
    assert_eq!(holon.constitutive.local.len(), 2);
    assert_eq!(holon.receiver.factors.len(), 2);
    assert_eq!(holon.reconstruction.collapsed_fibres.len(), 2);
    assert_eq!(holon.open_obligations.len(), 3);
}

#[test]
fn neutral_rested_surface_round_trips_the_existing_native_owner() {
    let scaffold = scaffold();
    RestedTransportEcology::validate_rest(&scaffold).expect("neutral validation");
    let bytes = RestedTransportEcology::canonical_rest_bytes(&scaffold).expect("neutral rest");
    assert_eq!(bytes, scaffold.canonical_bytes().expect("owner rest"));
    assert_eq!(
        NativeTransportScaffold::read(&bytes).expect("remount"),
        scaffold
    );
}

#[test]
#[ignore = "requires the resident CUDA native-word entry"]
fn neutral_rested_surface_conducts_the_existing_resident_word() {
    let scaffold = scaffold();
    let request = NativeTransportRequest {
        spool: "spool/native-turn".to_owned(),
        word: vec![InputId(7)],
        native_start: vec![NativeStateId(0), NativeStateId(1)],
        receiver: ReceiverId(9),
    };
    let neutral = RestedTransportEcology::conduct(&scaffold, &request).expect("neutral conduct");
    let mut direct = scaffold
        .mount_word(&request.spool, &request.word)
        .expect("direct mount");
    let direct = direct
        .conduct(&request.native_start, request.receiver)
        .expect("direct conduct");
    assert_eq!(neutral, direct);
    assert!(!neutral.apparatus.invariant_transport_reuploaded);
}

#[test]
fn exterior_configuration_names_cannot_move_the_intrinsic_native_profile() {
    let scaffold = scaffold();
    let before = scaffold
        .intrinsic_holon_profile()
        .expect("profile before exterior chart");
    let left = ForeignConfigurationChart::read(
        "left/config.json",
        br#"{"layer_types":["linear","full"],"n_routed_experts":288,"fmt":"e4m3"}"#.to_vec(),
    )
    .expect("left chart");
    let right = ForeignConfigurationChart::read(
        "right/config.json",
        br#"{"transport_kinds":["local","global"],"branch_population":288,"grain":"e4m3"}"#
            .to_vec(),
    )
    .expect("right chart");
    assert_ne!(left, right);
    let after = scaffold
        .intrinsic_holon_profile()
        .expect("profile after exterior chart");
    assert_eq!(before, after);
}

struct FixtureDismantlingReturn {
    productive: NativeTransportScaffold,
    cold: String,
    insufficiency: String,
}

impl DismantlingBoundaryReturn for FixtureDismantlingReturn {
    type Productive = NativeTransportScaffold;
    type ColdWitness = String;
    type Insufficiency = String;

    fn productive(&self) -> &Self::Productive {
        &self.productive
    }

    fn cold_witness(&self) -> &Self::ColdWitness {
        &self.cold
    }

    fn insufficiency(&self) -> &Self::Insufficiency {
        &self.insufficiency
    }
}

#[test]
fn dismantling_profile_borrows_only_the_productive_native_lane() {
    let returned = FixtureDismantlingReturn {
        productive: scaffold(),
        cold: "foreign architecture testimony".to_owned(),
        insufficiency: "unexcited receiver family".to_owned(),
    };
    let profiled = profile_dismantling_return(&returned).expect("profiled return");
    assert_eq!(profiled.productive_profile.holons.len(), 2);
    assert_eq!(
        profiled.returned.cold_witness().as_str(),
        returned.cold.as_str()
    );
    assert_eq!(
        profiled.returned.insufficiency().as_str(),
        returned.insufficiency.as_str()
    );
    assert!(std::ptr::eq(
        profiled.productive_profile.holons[0].morphology,
        &returned.productive.spools[0].threads[0]
    ));
}
