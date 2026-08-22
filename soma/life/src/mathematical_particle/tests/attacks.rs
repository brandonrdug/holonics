use super::*;

use holonic_engine::exact_owner_testimony::ExactOwnerKind;
use holonic_engine::interaction::{InteractionPattern, InteractionTemporality, OccurrencePort};
use holonic_engine::ported_operation::CandidateDiagrams;
use holonic_engine::source_occurrence::OccurrenceWitness;

#[test]
fn addressed_passage_retains_boundary_maps_and_pullback_occurrences() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let passage = &input.passages[0];
    let addressed = passage.addressed();
    assert_eq!(addressed.occurrences().len(), 4);
    assert_eq!(addressed.pullback_joins().len(), 2);
    assert_eq!(addressed.shadow_fibres().len(), 4);
    for join in addressed.pullback_joins() {
        let retained = addressed
            .split_rejoin(join.left(), join.right())
            .expect("the pullback occurrence must split without relation search");
        assert_eq!(retained, join);
        assert!(!join.interactions().is_empty());
        assert_eq!(
            addressed.occurrences()[&join.left()].target(),
            addressed.occurrences()[&join.right()].source()
        );
    }
    PassageEquivalence::found(
        addressed,
        addressed,
        addressed
            .occurrences()
            .keys()
            .map(|occurrence| (*occurrence, *occurrence))
            .collect(),
    )
    .expect("identity preserves both boundary maps");
}

#[test]
fn a_bare_occurrence_bijection_cannot_move_passage_boundaries() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let addressed = input.passages[0].addressed();
    let occurrences = addressed.occurrences().keys().copied().collect::<Vec<_>>();
    let mut moved = occurrences
        .iter()
        .map(|occurrence| (*occurrence, *occurrence))
        .collect::<BTreeMap<_, _>>();
    moved.insert(occurrences[0], occurrences[1]);
    moved.insert(occurrences[1], occurrences[0]);
    assert!(matches!(
        PassageEquivalence::found(addressed, addressed, moved),
        Err(MathematicalParticleError::PassageEquivalenceMovesBoundary { .. })
    ));
}

#[test]
fn one_relational_shadow_can_hide_two_carrying_occurrences() {
    use crate::mathematical_particle::lineage::{
        addressed_occurrence_for_control, AddressedPassage,
    };

    let source = PassageEndpoint::Ports(vec![holonic_engine::category::BoundaryId(11)]);
    let target = PassageEndpoint::Ports(vec![holonic_engine::category::BoundaryId(12)]);
    let occurrences = BTreeMap::from([
        (
            EventId(101),
            addressed_occurrence_for_control(
                EventId(101),
                EvolutionLawId(7),
                source.clone(),
                target.clone(),
            ),
        ),
        (
            EventId(102),
            addressed_occurrence_for_control(EventId(102), EvolutionLawId(7), source, target),
        ),
    ]);
    let passage = AddressedPassage::from_parts(occurrences, BTreeSet::new()).unwrap();
    assert_eq!(passage.occurrences().len(), 2);
    assert_eq!(passage.shadow_fibres().len(), 1);
    assert_eq!(passage.shadow_fibres().values().next().unwrap().len(), 2);
}

#[test]
fn a_shared_boundary_without_an_actual_interaction_bond_is_not_a_word() {
    let mut operation = PortedOperationComplex::new("false-shared-boundary");
    let p0 = operation.port("p0");
    let shared = operation.port("shared");
    let p2 = operation.port("p2");
    let first = operation
        .bind_operation(
            "first",
            OperationSpecies::Transport,
            vec![p0],
            vec![shared],
            None,
            Vec::new(),
        )
        .unwrap();
    let second = operation
        .bind_operation(
            "second",
            OperationSpecies::Transport,
            vec![shared],
            vec![p2],
            None,
            Vec::new(),
        )
        .unwrap();
    let first_event = operation.occur(first).unwrap();
    let second_event = operation.occur(second).unwrap();
    operation
        .shape
        .add_precedence(first_event, second_event)
        .unwrap();
    let steps = vec![
        OperationWordStep {
            event: first_event,
            law: first,
            inputs: vec![p0],
            outputs: vec![shared],
        },
        OperationWordStep {
            event: second_event,
            law: second,
            inputs: vec![shared],
            outputs: vec![p2],
        },
    ];
    let attempted = TypedOperationWord::found("false-word", steps.clone(), &operation);
    assert!(matches!(
        attempted,
        Err(MathematicalParticleError::WordInteractionAbsent { .. })
    ));
    operation
        .carries_precedence(
            "actual-bond",
            shared,
            OccurrencePort::output(first_event, 0),
            OccurrencePort::input(second_event, 0),
        )
        .unwrap();
    assert!(TypedOperationWord::found("actual-word", steps, &operation).is_ok());
}

#[test]
fn passage_terminals_must_share_one_actual_front() {
    let mut operation = PortedOperationComplex::new("serial-terminals");
    let p0 = operation.port("p0");
    let p1 = operation.port("p1");
    let p2 = operation.port("p2");
    let stage_first = operation
        .bind_operation(
            "stage-first",
            OperationSpecies::Construction,
            Vec::new(),
            vec![p0],
            None,
            Vec::new(),
        )
        .unwrap();
    let stage_second = operation
        .bind_operation(
            "stage-second",
            OperationSpecies::Construction,
            Vec::new(),
            vec![p0],
            None,
            Vec::new(),
        )
        .unwrap();
    let first = operation
        .bind_operation(
            "first",
            OperationSpecies::Transport,
            vec![p0],
            vec![p1],
            None,
            Vec::new(),
        )
        .unwrap();
    let second = operation
        .bind_operation(
            "second",
            OperationSpecies::Transport,
            vec![p0],
            vec![p2],
            None,
            Vec::new(),
        )
        .unwrap();
    let stage_first_event = operation.occur(stage_first).unwrap();
    let stage_second_event = operation.occur(stage_second).unwrap();
    let first_event = operation.occur(first).unwrap();
    let second_event = operation.occur(second).unwrap();
    operation
        .carries_precedence(
            "stage first",
            p0,
            OccurrencePort::output(stage_first_event, 0),
            OccurrencePort::input(first_event, 0),
        )
        .unwrap();
    operation
        .carries_precedence(
            "stage second",
            p0,
            OccurrencePort::output(stage_second_event, 0),
            OccurrencePort::input(second_event, 0),
        )
        .unwrap();
    operation
        .shape
        .add_precedence(first_event, second_event)
        .unwrap();
    let first_word = TypedOperationWord::found(
        "first-word",
        vec![OperationWordStep {
            event: first_event,
            law: first,
            inputs: vec![p0],
            outputs: vec![p1],
        }],
        &operation,
    )
    .unwrap();
    let second_word = TypedOperationWord::found(
        "second-word",
        vec![OperationWordStep {
            event: second_event,
            law: second,
            inputs: vec![p0],
            outputs: vec![p2],
        }],
        &operation,
    )
    .unwrap();
    let sources = BTreeSet::from(["source".to_owned()]);
    assert!(matches!(
        TypedPassage::found(
            "serial-passage",
            BTreeMap::from([
                (PassageBranchId(0), sources.clone()),
                (PassageBranchId(1), sources.clone()),
            ]),
            BTreeMap::from([
                (
                    PassageBranchId(0),
                    TypedConstructionStep {
                        event: stage_first_event,
                        law: stage_first,
                        outputs: vec![p0],
                    },
                ),
                (
                    PassageBranchId(1),
                    TypedConstructionStep {
                        event: stage_second_event,
                        law: stage_second,
                        outputs: vec![p0],
                    },
                ),
            ]),
            BTreeMap::from([
                (PassageBranchId(0), first_word),
                (PassageBranchId(1), second_word),
            ]),
            &operation,
            &sources,
        ),
        Err(MathematicalParticleError::BranchTerminalsNotCoPresent)
    ));
}

#[test]
fn an_exact_linear_return_cannot_substitute_an_unlicensed_matrix() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let passage = &input.passages[0];
    let branch = passage.branch(PassageBranchId(0)).unwrap();
    let wrong = PortedWord::founded(
        "wrong",
        vec![PortedTransport::new(
            "wrong-step",
            branch.source_port(),
            branch.target_port(),
            "wrong-chart",
            ExactRatMatrix::identity(2).unwrap(),
        )],
    )
    .unwrap();
    let licenses = input
        .admission
        .exact_owner
        .validate(&input.operation)
        .unwrap()
        .into_iter()
        .flat_map(|binding| binding.exact_owner_licenses)
        .filter(|license| license.owner() == ExactOwnerKind::ExactLinear)
        .map(|license| (license.constraint().law(), license))
        .collect::<BTreeMap<_, _>>();
    let matrices = BTreeMap::from([
        (
            passage.staging()[&PassageBranchId(0)].law,
            ExactRatMatrix::identity(2).unwrap(),
        ),
        (branch.steps[0].law, ExactRatMatrix::identity(2).unwrap()),
    ]);
    assert!(matches!(
        conduct_exact_linear(
            passage.reference(PassageBranchId(0)).unwrap(),
            passage,
            &wrong,
            &matrices,
            &licenses,
            &[integer(1), integer(1)],
        ),
        Err(MathematicalParticleError::ExactOwnerReturnDisagrees(_))
    ));
}

#[test]
fn returned_owner_evidence_must_equal_the_admitted_license() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    input.linear_returns[0].steps[0].owner_evidence_sha256 = "forged".to_owned();
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::AdmissionNotCausallyLinked)
    ));
}

#[test]
fn a_total_but_noncommuting_event_map_is_not_a_diagram_isomorphism() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let source_addresses = input
        .source_testimonies
        .iter()
        .flat_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|item| item.address.clone())
        })
        .collect::<Vec<_>>();
    let ports = input
        .operation
        .shape
        .boundaries
        .objects
        .keys()
        .copied()
        .collect::<Vec<_>>();
    let laws = input
        .operation
        .shape
        .laws
        .keys()
        .copied()
        .collect::<Vec<_>>();
    let events = input
        .operation
        .shape
        .occurrences
        .keys()
        .copied()
        .collect::<Vec<_>>();
    let words = input.passages[0]
        .branches()
        .values()
        .map(|word| word.occurrence.clone())
        .collect::<Vec<_>>();
    let event_map = events
        .iter()
        .enumerate()
        .map(|(at, event)| match at {
            0 => (*event, events[1]),
            1 => (*event, events[0]),
            _ => (*event, *event),
        })
        .collect();
    let interaction_map = input
        .operation
        .shape
        .interactions
        .keys()
        .map(|interaction| (*interaction, *interaction))
        .collect();
    let evidence = BTreeSet::from([
        source_addresses[0].clone(),
        source_addresses[1].clone(),
        "shared-passage".to_owned(),
        "linear-word".to_owned(),
        "quantity-word".to_owned(),
        "presentation-fibre".to_owned(),
        "open-fibre".to_owned(),
    ]);
    let source_set = source_addresses.iter().cloned().collect::<BTreeSet<_>>();
    let source_map = BTreeMap::from([
        (source_addresses[0].clone(), source_addresses[1].clone()),
        (source_addresses[1].clone(), source_addresses[0].clone()),
    ]);
    let port_map = ports
        .iter()
        .map(|port| (*port, *port))
        .collect::<BTreeMap<_, _>>();
    let law_map = laws
        .iter()
        .map(|law| (*law, *law))
        .collect::<BTreeMap<_, _>>();
    let word_map = words
        .iter()
        .map(|word| (word.clone(), word.clone()))
        .collect::<BTreeMap<_, _>>();
    let fibre_map = BTreeMap::from([
        (
            "presentation-fibre".to_owned(),
            "presentation-fibre".to_owned(),
        ),
        ("open-fibre".to_owned(), "open-fibre".to_owned()),
    ]);
    let attempted = MarkedDiagramRelation::found(
        source_map.clone(),
        port_map.clone(),
        law_map.clone(),
        event_map,
        interaction_map,
        word_map.clone(),
        fibre_map.clone(),
        RelationWitness::established(BTreeSet::from(["shared-passage".to_owned()])),
        &evidence,
        &source_set,
        &input.operation,
        &input.passages,
        &input.presentation_fibres,
        &input.open_fibres,
    );
    assert!(matches!(
        attempted,
        Err(MathematicalParticleError::MalformedRelation(
            "marked-diagram-isomorphism"
        ))
    ));

    let interaction_ids = input
        .operation
        .shape
        .interactions
        .keys()
        .copied()
        .collect::<Vec<_>>();
    let swapped_interactions = BTreeMap::from([
        (interaction_ids[0], interaction_ids[1]),
        (interaction_ids[1], interaction_ids[0]),
    ]);
    let identity_events = events.iter().map(|event| (*event, *event)).collect();
    let altered_bond = MarkedDiagramRelation::found(
        source_map,
        port_map,
        law_map,
        identity_events,
        swapped_interactions,
        word_map,
        fibre_map,
        RelationWitness::established(BTreeSet::from(["shared-passage".to_owned()])),
        &evidence,
        &source_set,
        &input.operation,
        &input.passages,
        &input.presentation_fibres,
        &input.open_fibres,
    );
    assert!(matches!(
        altered_bond,
        Err(MathematicalParticleError::MalformedRelation(
            "marked-diagram-isomorphism"
        ))
    ));
}

#[test]
fn a_typing_refusal_is_retained_without_aborting_the_accepted_particle() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let selection = PassageSelection::posed(
        "shared-passage",
        BTreeSet::from([PassageBranchId(u64::MAX)]),
    );
    let (proposal, refusal) =
        ParticleProposal::from_typing_result("proposal-c", selection, &input.passages).unwrap();
    input.proposals.push(proposal);
    input.refusals.push(refusal);
    input.open_fibres[0]
        .candidates
        .insert("proposal-c".to_owned());
    assert!(MathematicalParticle::found(input).is_ok());
}

#[test]
fn an_unlicensed_extra_occurrence_keeps_the_particle_open() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let law = input.operations[0].law;
    input.operation.occur(law).unwrap();
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::LicensedOccurrencesNotTotal)
    ));
}

#[test]
fn an_open_operation_question_prevents_closure() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    input.operation.retain_undecided(CandidateDiagrams {
        question: "which branch".to_owned(),
        candidates: vec!["left".to_owned(), "right".to_owned()],
        would_be_decided_by: vec!["receiver".to_owned()],
    });
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::OperationShapeOpen)
    ));
}

#[test]
fn binder_scope_must_cover_every_law_using_its_slot_port() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let quantity = input.operations[1].law;
    input.binders[0].laws.remove(&quantity);
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::BinderScopeDoesNotCover { .. })
    ));
}

#[test]
fn receiver_classification_and_similarity_relations_recheck_the_owned_returns() {
    let mut value_input = fixture().expect("required M1 GPU fixture must return");
    let source = value_input.value_receivers[0].source_occurrences.clone();
    let port = value_input.value_receivers[0].port();
    value_input.value_receivers[0] = ValueReceiverReturn::found(
        "value-receiver",
        port,
        source,
        vec![ExactValue::rational(integer(9))],
    )
    .unwrap();
    assert!(matches!(
        MathematicalParticle::found(value_input),
        Err(MathematicalParticleError::MalformedRelation(
            "receiver-face"
        ))
    ));

    let mut classification_input = fixture().expect("required M1 GPU fixture must return");
    let addresses = classification_input
        .source_testimonies
        .iter()
        .flat_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|item| item.address.clone())
        })
        .collect::<Vec<_>>();
    classification_input.classification_receivers[0] = ClassificationReceiverReturn::found(
        "classification-receiver",
        BTreeMap::from([
            (addresses[0].clone(), b"left".to_vec()),
            (addresses[1].clone(), b"right".to_vec()),
        ]),
    )
    .unwrap();
    assert!(matches!(
        MathematicalParticle::found(classification_input),
        Err(MathematicalParticleError::MalformedRelation(
            "classification"
        ))
    ));

    let mut similarity_input = fixture().expect("required M1 GPU fixture must return");
    similarity_input.similarity_receivers[0] = SimilarityReceiverReturn::found(
        "similarity-receiver",
        "different-frame",
        BTreeMap::from([
            (
                addresses[0].clone(),
                BTreeMap::from([("cross-ratio".to_owned(), b"-1".to_vec())]),
            ),
            (
                addresses[1].clone(),
                BTreeMap::from([("cross-ratio".to_owned(), b"+1".to_vec())]),
            ),
        ]),
    )
    .unwrap();
    assert!(matches!(
        MathematicalParticle::found(similarity_input),
        Err(MathematicalParticleError::MalformedRelation(
            "characteristic-similarity"
        ))
    ));
}

#[test]
fn actual_receiver_history_decides_shared_and_separated_cases() {
    let left = "left";
    let right = "right";
    let shared =
        ReceiverHistoryReturn::found("shared-history", history_reading(left, right)).unwrap();
    let shared_relation = ReceiverHistoryRelation::from_return(left, right, &shared).unwrap();
    assert!(matches!(
        shared_relation.witness(),
        RelationWitness::Established { .. }
    ));

    let mut separated_reading = history_reading(left, right);
    separated_reading.root_conduct_blocks = vec![
        BTreeSet::from([left.to_owned()]),
        BTreeSet::from([right.to_owned()]),
    ];
    separated_reading.shortest_separators = vec![crate::causal_section::SectionSeparator {
        left: left.to_owned(),
        right: right.to_owned(),
        interventions: vec!["advance".to_owned()],
        receiver: Some("exact-value".to_owned()),
        left_observation: Some("0".to_owned()),
        right_observation: Some("1".to_owned()),
        separated_by_terminus: false,
    }];
    let separated = ReceiverHistoryReturn::found("separated-history", separated_reading).unwrap();
    let separated_relation = ReceiverHistoryRelation::from_return(left, right, &separated).unwrap();
    assert!(matches!(
        separated_relation.witness(),
        RelationWitness::Separated { .. }
    ));
}

#[test]
fn one_exact_deed_can_only_leave_two_presentation_histories_open() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let addresses = input
        .source_testimonies
        .iter()
        .flat_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|item| item.address.clone())
        })
        .collect::<Vec<_>>();
    let deed = input
        .admission
        .passage_receipt
        .as_ref()
        .expect("the admitted M1 particle requires its post-card deed receipt");
    let returned = ReceiverHistoryReturn::open_from_exact_deed(
        "one-deed-history",
        &addresses[0],
        &addresses[1],
        deed,
    )
    .unwrap();
    assert!(returned.reading().root_one_shot_blocks.is_empty());
    assert!(returned.reading().root_conduct_blocks.is_empty());
    assert!(returned.reading().shortest_separators.is_empty());

    let relation =
        ReceiverHistoryRelation::from_return(&addresses[0], &addresses[1], &returned).unwrap();
    assert!(matches!(relation.witness(), RelationWitness::Open { .. }));
}

#[test]
fn a_word_refuses_missing_and_fake_input_ports() {
    let mut operation = PortedOperationComplex::new("port-word");
    let input = operation.port("input");
    let output = operation.port("output");
    let fake = operation.port("fake");
    let law = operation
        .bind_operation(
            "transport",
            OperationSpecies::Transport,
            vec![input],
            vec![output],
            None,
            Vec::new(),
        )
        .unwrap();
    let event = operation.occur(law).unwrap();
    for offered in [Vec::new(), vec![fake]] {
        assert!(matches!(
            TypedOperationWord::found(
                "bad-port-word",
                vec![OperationWordStep {
                    event,
                    law,
                    inputs: offered,
                    outputs: vec![output],
                }],
                &operation,
            ),
            Err(MathematicalParticleError::WordStepOutsideLaw(_))
        ));
    }
}

#[test]
fn every_selected_branch_returns_exactly_once_and_requires_resident_entailment() {
    let mut duplicate = fixture().expect("required M1 GPU fixture must return");
    duplicate
        .linear_returns
        .push(duplicate.linear_returns[0].clone());
    assert!(matches!(
        MathematicalParticle::found(duplicate),
        Err(MathematicalParticleError::AdmissionNotCausallyLinked)
    ));

    let mut cpu_only = fixture().expect("required M1 GPU fixture must return");
    cpu_only.admission.passage_receipt = None;
    assert!(matches!(
        MathematicalParticle::found(cpu_only),
        Err(MathematicalParticleError::MissingResidentPassageReceipt)
    ));
}

#[test]
fn a_zero_returning_deed_receipt_cannot_cross_into_an_altered_interaction_complex() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let receipt = input
        .admission
        .passage_receipt
        .as_ref()
        .expect("the required fixture carries its actual post-card receipt")
        .clone();
    let selected = receipt
        .entailed_occurrences()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    assert!(receipt.matches_complex_and_selection(&input.operation, &selected));
    let terminal_events = input.passages[0]
        .branches()
        .values()
        .map(|word| word.steps.last().expect("nonempty branch").event)
        .collect::<BTreeSet<_>>();
    assert!(terminal_events.iter().all(|terminal| {
        receipt
            .readbacks()
            .get(terminal)
            .expect("terminal readback")
            .iter()
            .all(|word| *word == (0, 0))
    }));

    let original = input
        .operation
        .shape
        .interactions
        .values()
        .next()
        .expect("fixture interaction")
        .clone();
    input
        .operation
        .shape
        .add_interaction(InteractionPattern::new(
            "additional incidence with the same nominal law/event population",
            original.boundary,
            InteractionTemporality::CarriesPrecedence,
            original.bonds,
        ))
        .unwrap();
    assert!(!receipt.matches_complex_and_selection(&input.operation, &selected));
    assert!(MathematicalParticle::found(input).is_err());
}

#[test]
fn display_renaming_does_not_move_the_deed_complex_identity() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let receipt = input
        .admission
        .passage_receipt
        .as_ref()
        .expect("the required fixture carries its actual post-card receipt")
        .clone();
    let selected = receipt
        .entailed_occurrences()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    input.operation.name = "renamed complex".to_owned();
    for boundary in input.operation.shape.boundaries.objects.values_mut() {
        boundary.name = "renamed boundary".to_owned();
    }
    for law in input.operation.shape.laws.values_mut() {
        law.name = "renamed law".to_owned();
    }
    for event in input.operation.shape.chronology.events.values_mut() {
        event.law = "renamed chronology display".to_owned();
    }
    for interaction in input.operation.shape.interactions.values_mut() {
        interaction.name = "renamed interaction".to_owned();
    }
    assert!(receipt.matches_complex_and_selection(&input.operation, &selected));
    let boundaries = input
        .operation
        .shape
        .boundaries
        .objects
        .keys()
        .copied()
        .take(2)
        .collect::<Vec<_>>();
    input
        .operation
        .shape
        .boundaries
        .add_arrow("new incidence", boundaries[0], boundaries[1])
        .unwrap();
    assert!(!receipt.matches_complex_and_selection(&input.operation, &selected));
}

#[test]
fn a_public_embedded_id_cannot_hide_behind_its_canonical_map_key() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let receipt = input
        .admission
        .passage_receipt
        .as_ref()
        .expect("the required fixture carries its actual post-card receipt")
        .clone();
    let selected = receipt
        .entailed_occurrences()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    assert!(receipt.matches_complex_and_selection(&input.operation, &selected));

    let key = *input
        .operation
        .shape
        .boundaries
        .objects
        .keys()
        .next()
        .expect("fixture boundary");
    input
        .operation
        .shape
        .boundaries
        .objects
        .get_mut(&key)
        .expect("addressed boundary")
        .id = holonic_engine::category::BoundaryId(u64::MAX);
    assert!(!receipt.matches_complex_and_selection(&input.operation, &selected));
    assert!(MathematicalParticle::found(input).is_err());
}

#[test]
fn quantity_return_uses_the_licensed_kernel_not_the_raw_product() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let returned = &input.quantity_returns[0];
    let mut raw = returned.factors()[0].clone();
    for factor in &returned.factors()[1..] {
        raw = raw.product(factor).unwrap();
    }
    assert!(!raw.dimension().is_dimensionless());
    assert!(returned.returned().dimension().is_dimensionless());
    assert_eq!(
        returned.kernel_word(),
        &[integer(1), integer(1), integer(-2)]
    );

    let passage = &input.passages[0];
    let dimensions = returned.dimension_matrix().clone();
    let columns = returned.boundary_columns().clone();
    let mut licenses = input
        .admission
        .exact_owner
        .validate(&input.operation)
        .unwrap()
        .into_iter()
        .flat_map(|binding| binding.exact_owner_licenses)
        .filter(|license| license.owner() == ExactOwnerKind::Quantity)
        .map(|license| (license.constraint().law(), license))
        .collect::<BTreeMap<_, _>>();
    let contract_law = passage.branch(PassageBranchId(1)).unwrap().steps[0].law;
    let original = licenses[&contract_law].clone();
    let altered = ExactOwnerLicense::quantity(
        contract_law,
        "altered-kernel",
        original.constraint().resident_law(),
        original.constraint().species(),
        original.constraint().inputs().to_vec(),
        original.constraint().outputs().to_vec(),
        columns[&contract_law].clone(),
        &dimensions,
        &[integer(1), integer(-1), integer(0)],
        original.constraint().semantic_parameters().clone(),
    )
    .unwrap();
    licenses.insert(contract_law, altered);
    assert!(matches!(
        conduct_exact_quantity(
            passage.reference(PassageBranchId(1)).unwrap(),
            passage,
            dimensions,
            columns,
            &licenses,
            returned.factors().to_vec(),
        ),
        Err(MathematicalParticleError::ExactOwnerReturnDisagrees(_))
    ));
}

#[test]
fn one_boundary_cannot_receive_conflicting_types_from_two_licenses() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    let returned = &input.quantity_returns[0];
    let dimensions = returned.dimension_matrix().clone();
    let columns = returned.boundary_columns().clone();
    let contract_law = input.passages[0].branch(PassageBranchId(1)).unwrap().steps[0].law;
    let mut licenses = input
        .admission
        .exact_owner
        .validate(&input.operation)
        .unwrap()
        .into_iter()
        .flat_map(|binding| binding.exact_owner_licenses)
        .collect::<Vec<_>>();
    let at = licenses
        .iter()
        .position(|license| license.constraint().law() == contract_law)
        .unwrap();
    let original = licenses[at].clone();
    let input_boundary = &original.constraint().inputs()[0];
    let conflicting = TypedMathematicalBoundary::coordinate_word(
        input_boundary.boundary(),
        "R",
        input_boundary.dimensions().to_vec(),
        input_boundary.tensor_slots().to_vec(),
    )
    .unwrap();
    licenses[at] = ExactOwnerLicense::quantity(
        contract_law,
        "conflicting-carrier",
        original.constraint().resident_law(),
        original.constraint().species(),
        vec![conflicting],
        original.constraint().outputs().to_vec(),
        columns[&contract_law].clone(),
        &dimensions,
        original.constraint().quantity_kernel_word().unwrap(),
        original.constraint().semantic_parameters().clone(),
    )
    .unwrap();
    input.admission.exact_owner = ExactOwnerOccurrence::new(licenses).unwrap();
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::ConflictingBoundaryLicense(_))
    ));
}
