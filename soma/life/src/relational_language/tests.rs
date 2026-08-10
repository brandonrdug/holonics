use super::*;
use super::{codec::*, transport::*};
use soma_membrane::{
    CurrentExecutionRequest, DirectedExecutionRequest, ExecutedContemporaryEvent, LiveCurrentError,
    RegionalExecutionRequest,
};

const TEST_RECEIVER_HORIZON: u64 = 16;

trait RelationalTestInspection {
    fn closed_thought_at_declared_horizon(
        &self,
        question: &str,
    ) -> Result<Option<RelationalThoughtCurrent>, RelationalLanguageError>;
}

impl RelationalTestInspection for ExactRelationalLanguageEcology {
    fn closed_thought_at_declared_horizon(
        &self,
        question: &str,
    ) -> Result<Option<RelationalThoughtCurrent>, RelationalLanguageError> {
        Ok(self
            .think_fiber(question, TEST_RECEIVER_HORIZON)?
            .and_then(|fiber| fiber.closed().next().cloned()))
    }
}

struct RefusingExecutor;

impl LiveCurrentExecutor for RefusingExecutor {
    fn enact(
        &mut self,
        _physical_revision: u64,
        _standing: &SparseStandingSurface,
        _currents: &[CurrentExecutionRequest<'_>],
        _relations: &[DirectedExecutionRequest],
        _regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        Err(LiveCurrentError::PhysicalSettlement)
    }
}

fn passages() -> Vec<MorphologicalLanguagePassage> {
    vec![MorphologicalLanguagePassage::new(
        "continuity",
        "continuity-source",
        1,
        "One returned token advances those exact suffix currents. The next emanation is formed from the advanced currents themselves.",
    )]
}

#[test]
fn source_clauses_found_a_connected_thought_with_source_absent_wording() {
    let ecology = ExactRelationalLanguageEcology::condition(&passages()).unwrap();
    let thought = ecology
        .closed_thought_at_declared_horizon(
            "How does one returned token change the exact suffix current used by the next emanation?",
        )
        .unwrap()
        .unwrap();
    assert!(thought.is_closed());
    assert_eq!(thought.clauses.len(), 2);
    assert_eq!(thought.joins.len(), 1);
    assert_eq!(thought.transport.components.len(), 1);
    assert!(thought.transport.passages.is_empty());
    assert!(thought.transport.ordered_transport_product.is_empty());
    assert_eq!(thought.transport.receiver_horizon, 0);
    assert!(thought.transport.boundary_storage.is_empty());
    let selected = thought.selected().unwrap();
    assert!(selected.voice_dual);
    assert!(!selected.inherited_contiguous);
    assert_eq!(
        selected.text,
        "Those exact suffix currents are advanced by one returned token. The advanced currents themselves form the next emanation."
    );
    assert!(selected
        .clauses
        .iter()
        .all(|clause| !clause.inherited_contiguous));
}

#[test]
fn deliberative_regions_remain_copresent_without_cartesian_set_cover() {
    let ecology = ExactRelationalLanguageEcology::condition(&[MorphologicalLanguagePassage::new(
        "copresent-chain",
        "chain-source",
        1,
        "Alpha carries beta. Beta carries gamma. Gamma restricts delta.",
    )])
    .unwrap();
    let returned = ecology
        .think_deliberative_fiber_over_regions(
            "How could beta and delta inform epsilon?",
            &[
                BTreeSet::from(["beta".to_owned()]),
                BTreeSet::from(["delta".to_owned()]),
                BTreeSet::from(["epsilon".to_owned()]),
            ],
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();

    assert!(!returned.currents.is_empty());
    assert!(returned.currents.iter().all(|current| !current.is_closed()));
    assert_eq!(
        returned.unreturned_question_regions,
        vec![BTreeSet::from(["epsilon".to_owned()])]
    );
    assert!(!returned.is_closed());

    let complete = ecology
        .think_deliberative_fiber_over_regions(
            "How could beta and delta interact?",
            &[
                BTreeSet::from(["beta".to_owned()]),
                BTreeSet::from(["delta".to_owned()]),
            ],
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();
    assert!(complete.is_closed());
    assert!(complete.unreturned_question_regions.is_empty());
}

#[test]
fn a_separated_junction_opens_then_recurring_phase_conducts_as_a_ride() {
    let first = vec![
        MorphologicalLanguagePassage::new(
            "first-retention",
            "first-retention-source",
            1,
            "Alpha retains nexus.",
        ),
        MorphologicalLanguagePassage::new(
            "first-preservation",
            "first-preservation-source",
            2,
            "Gamma preserves nexus.",
        ),
    ];
    let later = vec![
        MorphologicalLanguagePassage::new(
            "second-retention",
            "second-retention-source",
            3,
            "Delta retains nexus.",
        ),
        MorphologicalLanguagePassage::new(
            "second-preservation",
            "second-preservation-source",
            4,
            "Epsilon preserves nexus.",
        ),
    ];
    let regions = [
        BTreeSet::from(["alpha".to_owned()]),
        BTreeSet::from(["gamma".to_owned()]),
    ];

    let mut ecology = ExactRelationalLanguageEcology::condition(&first).unwrap();
    let open = ecology
        .think_deliberative_fiber_over_regions(
            "How do alpha and gamma meet?",
            &regions,
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();
    assert_eq!(open.closed().count(), 0);
    assert!(open.open_channel_boundaries.iter().any(|channel| {
        channel.conduct == RelationalChannelConduct::Open
            && channel.recurrence_population == BigUint::from(1u8)
    }));

    ecology.receive(&later).unwrap();
    assert!(
        ecology
            .junction_returns
            .iter()
            .any(|(_, returned)| matches!(
                returned.conduct(),
                ResonanceOccurrenceConduct::Complete { .. }
            )),
        "exact junction returns were {:?}",
        ecology.junction_returns
    );
    let returned = ecology
        .think_deliberative_fiber_over_regions(
            "How do alpha and gamma meet?",
            &regions,
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();
    assert!(returned.is_closed());
    assert!(returned
        .currents
        .iter()
        .flat_map(|current| &current.joins)
        .any(|join| {
            join.conduct == RelationalChannelConduct::Ride
                && join.recurrence_population >= BigUint::from(2u8)
        }));

    let mut reversed = first;
    reversed.extend(later);
    reversed.reverse();
    let reversed_ecology = ExactRelationalLanguageEcology::condition(&reversed).unwrap();
    assert_eq!(ecology.passage_delivery_order("first-retention"), Some(0));
    assert_eq!(
        reversed_ecology.passage_delivery_order("first-retention"),
        Some(3)
    );
    let reversed_return = reversed_ecology
        .think_deliberative_fiber_over_regions(
            "How do alpha and gamma meet?",
            &regions,
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();
    assert!(reversed_return.is_closed());
    assert_eq!(ecology.adjacency, reversed_ecology.adjacency);
    assert_eq!(ecology.current_passages, reversed_ecology.current_passages);
    assert_ne!(
        returned, reversed_return,
        "the same recurrent relation may conduct after either delivery, but its enacted transport chronology is not gauge"
    );
    assert_ne!(
        returned.currents[0].clauses[0].passage,
        reversed_return.currents[0].clauses[0].passage
    );
}

#[test]
fn equal_arrival_predecessors_remain_factorized_behind_receiver_sections() {
    let ecology = ExactRelationalLanguageEcology::condition(&[
        MorphologicalLanguagePassage::new("root", "root-source", 1, "Alpha carries beta."),
        MorphologicalLanguagePassage::new("left-branch", "left-source", 2, "Beta forms relay."),
        MorphologicalLanguagePassage::new("right-branch", "right-source", 3, "Beta changes relay."),
        MorphologicalLanguagePassage::new("return", "return-source", 4, "Relay carries omega."),
    ])
    .unwrap();
    let fiber = ecology
        .think_fiber_over_regions(
            "How does alpha reach omega?",
            &[
                BTreeSet::from(["alpha".to_owned()]),
                BTreeSet::from(["omega".to_owned()]),
            ],
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();
    let root_clause = "root::relation::0:0".to_owned();
    let left_clause = "left-branch::relation::0:0".to_owned();
    let right_clause = "right-branch::relation::0:0".to_owned();
    let return_clause = "return::relation::0:0".to_owned();
    let front = fiber
        .causal_front_fibers
        .iter()
        .find(|front| front.source_clauses.contains(&root_clause))
        .expect("the root receiver section must retain its causal front");
    assert_eq!(
        front.exact_path_populations.get(&return_clause),
        Some(&BigUint::from(2_u8))
    );
    assert_eq!(
        front.predecessor_incidence.get(&return_clause),
        Some(&LocalSet::from([left_clause, right_clause]))
    );
}

#[test]
fn the_same_relation_body_has_two_distinct_surface_realizations() {
    let ecology = ExactRelationalLanguageEcology::condition(&passages()).unwrap();
    let thought = ecology
        .closed_thought_at_declared_horizon(
            "How does the returned token affect the suffix current used by the emanation?",
        )
        .unwrap()
        .unwrap();
    assert!(thought.realizations.len() >= 2);
    assert_ne!(thought.realizations[0].text, thought.realizations[1].text);
    assert_eq!(thought.realizations[0].clauses.len(), 2);
    assert_eq!(thought.realizations[1].clauses.len(), 2);
}

#[test]
fn a_missing_entity_region_remains_open_instead_of_reusing_prior_language() {
    let ecology = ExactRelationalLanguageEcology::condition(&passages()).unwrap();
    assert!(ecology
        .closed_thought_at_declared_horizon("What is photosynthesis?")
        .unwrap()
        .is_none());
}

#[test]
fn a_definition_can_reverse_without_copying_its_source_surface() {
    let ecology = ExactRelationalLanguageEcology::condition(&[
        MorphologicalLanguagePassage::new(
            "definition",
            "definition-source",
            3,
            "ExactSuffixEcology is a generalized exact suffix automaton over arbitrary ResonanceGerm paths.",
        ),
    ])
    .unwrap();
    let thought = ecology
        .closed_thought_at_declared_horizon("What is ExactSuffixEcology?")
        .unwrap()
        .unwrap();
    let selected = thought.selected().unwrap();
    assert!(!selected.inherited_contiguous);
    assert_eq!(
        selected.text,
        "A generalized exact suffix automaton over arbitrary ResonanceGerm paths defines ExactSuffixEcology."
    );
}

#[test]
fn coordinated_questions_retain_passage_copresent_clauses_as_one_thought() {
    let ecology = ExactRelationalLanguageEcology::condition(&[
        MorphologicalLanguagePassage::new(
            "correction",
            "dialogue/correction",
            9,
            "The next emanation is formed from the advanced currents themselves, while the observer aperture restricts terminal testimony rather than truncating the causal current population.",
        ),
    ])
    .unwrap();
    let thought = ecology
        .closed_thought_at_declared_horizon(
            "What forms the next emanation, and what does the observer aperture restrict?",
        )
        .unwrap()
        .unwrap();
    assert_eq!(thought.clauses.len(), 2);
    assert_eq!(thought.joins.len(), 1);
    assert_eq!(
        thought.joins[0].shared_passage.as_deref(),
        Some("correction")
    );
    assert_eq!(thought.selected().unwrap().clauses.len(), 2);
}

#[test]
fn one_large_passage_retains_a_factorized_co_present_cell_not_a_clause_clique() {
    let clause_population = 128usize;
    let text = (0..clause_population)
        .map(|at| format!("Subject{at} carries Object{at}."))
        .collect::<Vec<_>>()
        .join(" ");
    let ecology = ExactRelationalLanguageEcology::condition(&[MorphologicalLanguagePassage::new(
        "large-cell",
        "large-source",
        12,
        text,
    )])
    .unwrap();
    let structural_edges = ecology.adjacency.iter().map(LocalSet::len).sum::<usize>() / 2;
    assert_eq!(ecology.clauses.len(), clause_population);
    assert_eq!(structural_edges, clause_population - 1);
    assert_eq!(ecology.junction_phases.len(), clause_population - 1);
    assert_eq!(ecology.current_passages.len(), clause_population - 1);
    assert_eq!(
        ecology
            .passage_incidence
            .get(&"large-cell".to_owned())
            .unwrap()
            .len(),
        clause_population
    );
}

#[test]
fn a_passive_occurrence_retains_its_copular_parse_as_an_open_fiber() {
    let ecology = ExactRelationalLanguageEcology::condition(&[MorphologicalLanguagePassage::new(
        "ambiguous-proof",
        "proof-source",
        11,
        "The proof is checked by the verifier.",
    )])
    .unwrap();
    assert_eq!(ecology.clauses().len(), 1);
    assert_eq!(ecology.parse_fibers().len(), 1);
    assert_eq!(ecology.parse_fibers()[0].alternatives.len(), 2);
    assert_eq!(
        ecology.parse_fibers()[0].alternatives[0].witnessed_voice,
        RelationalClauseVoice::Passive
    );
    assert_eq!(
        ecology.parse_fibers()[0].alternatives[1].witnessed_voice,
        RelationalClauseVoice::Copular
    );

    let thought = ecology
        .closed_thought_at_declared_horizon("What checks the proof?")
        .unwrap()
        .expect("the witnessed passive traversal must return the proof region");
    assert_eq!(thought.parse_fibers.len(), 1);
    assert_eq!(thought.parse_fibers[0].alternatives.len(), 2);
    assert!(thought.realizations.iter().any(|realization| {
        realization
            .clauses
            .iter()
            .any(|clause| clause.relation_clause.ends_with("::alternative::copular"))
    }));
    assert_eq!(thought.factorized_parse_population, BigUint::from(2u8));
}

#[test]
fn parse_products_remain_factorized_while_each_local_alternative_is_visible() {
    let text = (0..20)
        .map(|at| format!("Proof{at} is checked by verifier{at}."))
        .collect::<Vec<_>>()
        .join(" ");
    let ecology = ExactRelationalLanguageEcology::condition(&[MorphologicalLanguagePassage::new(
        "many-ambiguities",
        "proof-source",
        15,
        text,
    )])
    .unwrap();
    assert_eq!(ecology.clauses.len(), 20);
    assert!(ecology
        .parse_fibers
        .iter()
        .all(|fiber| fiber.alternatives.len() == 2));

    let population = parse_fiber_population(&ecology.clauses, &ecology.parse_fibers);
    assert_eq!(population, BigUint::from(1u64 << 20));
    let realizations = realize_relation_fibers(
        &ecology.clauses,
        &ecology.parse_fibers,
        &ecology.inherited_surfaces,
    )
    .unwrap();
    // Selected path plus twenty one-fiber variations, each with at most two voice sections.
    assert!(realizations.len() <= 42, "{}", realizations.len());
    assert!(realizations.iter().any(|realization| {
        realization
            .clauses
            .iter()
            .any(|clause| clause.relation_clause.ends_with("::alternative::copular"))
    }));
}

#[test]
fn a_deictic_clause_retains_its_caused_predecessor() {
    let ecology =
        ExactRelationalLanguageEcology::condition(&[MorphologicalLanguagePassage::new(
            "audit",
            "audit-source",
            12,
            "The function locally reconstructs relational ecology. This call path carries a continuity obstruction for relational morphology.",
        )])
        .unwrap();
    let thought = ecology
        .closed_thought_at_declared_horizon(
            "What carries a continuity obstruction for relational morphology?",
        )
        .unwrap()
        .unwrap();
    assert_eq!(thought.clauses.len(), 2, "{:#?}", thought.clauses);
    assert!(thought
        .selected()
        .unwrap()
        .text
        .to_lowercase()
        .contains("function"));
}

#[test]
fn equal_minimal_relation_traversals_remain_plural() {
    let ecology = ExactRelationalLanguageEcology::condition(&[
        MorphologicalLanguagePassage::new(
            "first-check",
            "first-source",
            13,
            "The first verifier checks the proof.",
        ),
        MorphologicalLanguagePassage::new(
            "second-check",
            "second-source",
            14,
            "The second verifier checks the proof.",
        ),
    ])
    .unwrap();
    let fiber = ecology
        .think_fiber("Who checks the proof?", TEST_RECEIVER_HORIZON)
        .unwrap()
        .unwrap();

    assert_eq!(fiber.closed().count(), 2);
    assert!(fiber.open().next().is_none());
    assert_eq!(
        fiber
            .closed()
            .map(|current| current.source_witnesses.clone())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            BTreeSet::from(["first-source".to_owned()]),
            BTreeSet::from(["second-source".to_owned()]),
        ])
    );
}

#[test]
fn a_passage_aperture_restricts_one_mounted_plural_relation_body() {
    let ecology = ExactRelationalLanguageEcology::condition(&[
        MorphologicalLanguagePassage::new(
            "first-check",
            "first-source",
            13,
            "The first verifier checks the proof.",
        ),
        MorphologicalLanguagePassage::new(
            "second-check",
            "second-source",
            14,
            "The second verifier checks the proof.",
        ),
    ])
    .unwrap();

    let fiber = ecology
        .think_fiber_in_passages(
            "Who checks the proof?",
            &BTreeSet::from(["second-check".to_owned()]),
            TEST_RECEIVER_HORIZON,
        )
        .unwrap()
        .unwrap();
    let closed = fiber.closed().collect::<Vec<_>>();
    assert_eq!(closed.len(), 1);
    assert_eq!(
        closed[0].passage_witnesses,
        BTreeSet::from(["second-check".to_owned()])
    );
    assert_eq!(ecology.clauses().len(), 2);
}

#[test]
fn modal_coordinate_ellipsis_preserves_two_relations_and_lawful_passive_case() {
    let passages = vec![MorphologicalLanguagePassage::new(
        "dialogue-user",
        "dialogue/user",
        41,
        "We could up the scale of training and condition the machine on our conversation log history.",
    )];
    let ecology = ExactRelationalLanguageEcology::condition(&passages).unwrap();
    assert!(ecology
        .clauses()
        .iter()
        .any(|clause| clause.relation == "up" && clause.modality.as_deref() == Some("could")));
    assert!(ecology.clauses().iter().any(|clause| {
        clause.relation == "condition" && clause.modality.as_deref() == Some("could")
    }));
    let current = ecology
        .closed_thought_at_declared_horizon("How do we condition the machine?")
        .unwrap()
        .expect("the carried coordinated predicate answers");
    let selected = current.selected().expect("a realization");
    assert!(selected.clauses.iter().any(|realized| {
        ecology.clauses().iter().any(|clause| {
            clause.identity == realized.relation_clause
                && clause.relation == "up"
                && clause.modality.as_deref() == Some("could")
        })
    }));
    assert!(selected.clauses.iter().any(|realized| {
        ecology.clauses().iter().any(|clause| {
            clause.identity == realized.relation_clause
                && clause.relation == "condition"
                && clause.modality.as_deref() == Some("could")
        })
    }));
    let modal_question = ecology
        .closed_thought_at_declared_horizon(
            "How could we condition the machine on our conversation log history?",
        )
        .unwrap()
        .expect("the modal question retains its subject and object regions");
    assert!(modal_question.is_closed());
    assert_eq!(modal_question.required_entity_regions.len(), 2);
}

#[test]
fn a_content_clause_is_one_outer_patient_despite_its_plural_interior() {
    let ecology =
        ExactRelationalLanguageEcology::condition(&[MorphologicalLanguagePassage::new(
            "verification",
            "code-return",
            42,
            "Exact Rust execution verifies that open currents emit bridge leaders until the relation closes.",
        )])
        .unwrap();
    let current = ecology
        .closed_thought_at_declared_horizon("What does exact Rust execution verify?")
        .unwrap()
        .unwrap();
    assert_eq!(
        current.selected().unwrap().text,
        "That open currents emit bridge leaders until the relation closes is verified by exact Rust execution."
    );
}

#[test]
fn worker_aperture_cannot_multiply_or_reorder_the_relation_organ() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "retention-a",
            "retention-source-a",
            1,
            "Alpha retains nexus. Sigma carries field.",
        ),
        MorphologicalLanguagePassage::new(
            "preservation-a",
            "preservation-source-a",
            2,
            "Gamma preserves nexus. Tau changes field.",
        ),
        MorphologicalLanguagePassage::new(
            "retention-b",
            "retention-source-b",
            3,
            "Delta retains nexus. Upsilon carries field.",
        ),
        MorphologicalLanguagePassage::new(
            "preservation-b",
            "preservation-source-b",
            4,
            "Epsilon preserves nexus. Phi changes field.",
        ),
    ];
    let serial = ExactRelationalLanguageEcology::condition_with_workers(&passages, 1).unwrap();
    let parallel = ExactRelationalLanguageEcology::condition_with_workers(&passages, 4).unwrap();
    assert_eq!(serial.clauses, parallel.clauses);
    assert_eq!(serial.adjacency, parallel.adjacency);
    assert_eq!(serial.junction_phases, parallel.junction_phases);
    assert_eq!(serial.junction_returns, parallel.junction_returns);
    assert_eq!(serial.current_passages, parallel.current_passages);
    let serial_execution = serial.execution_receipt();
    let parallel_execution = parallel.execution_receipt();
    assert_eq!(serial_execution.requested_worker_threads, 1);
    assert_eq!(parallel_execution.requested_worker_threads, 4);
    assert_eq!(serial_execution.pending_junctions, 0);
    assert_eq!(parallel_execution.pending_junctions, 0);
    assert_eq!(
        serial_execution.association_memory,
        parallel_execution.association_memory
    );
    assert_eq!(
        serial.association.rest_image().unwrap(),
        parallel.association.rest_image().unwrap()
    );
    let serial_thought = serial
        .think_fiber_with_execution("Who retains nexus?", TEST_RECEIVER_HORIZON)
        .unwrap();
    let parallel_thought = parallel
        .think_fiber_with_execution("Who retains nexus?", TEST_RECEIVER_HORIZON)
        .unwrap();
    assert_eq!(serial_thought.fiber, parallel_thought.fiber);
    let serial_cpu = serial_thought.cpu.unwrap();
    let parallel_cpu = parallel_thought.cpu.unwrap();
    assert_eq!(serial_cpu.tasks, parallel_cpu.tasks);
    assert_eq!(serial_cpu.workers_used, BigUint::from(1_u8));
    assert!(parallel_cpu.workers_used > BigUint::from(1_u8));

    let copresent_one =
        ExactRelationalLanguageEcology::condition_copresent_with_workers(&passages, 1).unwrap();
    let copresent_many =
        ExactRelationalLanguageEcology::condition_copresent_with_workers(&passages, 4).unwrap();
    assert_eq!(copresent_one.clauses, copresent_many.clauses);
    assert_eq!(copresent_one.adjacency, copresent_many.adjacency);
    assert_eq!(
        copresent_one.current_passages,
        copresent_many.current_passages
    );
    assert_eq!(
        copresent_one.association.rest_image().unwrap(),
        copresent_many.association.rest_image().unwrap()
    );
    assert_eq!(copresent_many.execution_receipt().pending_junctions, 0);
    let reversed_passages = passages.iter().rev().cloned().collect::<Vec<_>>();
    let copresent_reversed =
        ExactRelationalLanguageEcology::condition_copresent_with_workers(&reversed_passages, 4)
            .unwrap();
    assert_eq!(copresent_many.clauses, copresent_reversed.clauses);
    assert_eq!(copresent_many.adjacency, copresent_reversed.adjacency);
    assert_eq!(
        copresent_many.current_passages,
        copresent_reversed.current_passages
    );
    assert_eq!(
        copresent_many.association.rest_image().unwrap(),
        copresent_reversed.association.rest_image().unwrap()
    );
    assert_eq!(
        copresent_many.execution_receipt(),
        copresent_reversed.execution_receipt()
    );
}

#[test]
fn one_to_one_junction_returns_preserve_successors_across_later_histories() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "retains-a",
            "retains-source-a",
            1,
            "Alpha retains nexus.",
        ),
        MorphologicalLanguagePassage::new(
            "retains-b",
            "retains-source-b",
            2,
            "Beta retains nexus.",
        ),
        MorphologicalLanguagePassage::new(
            "retains-c",
            "retains-source-c",
            3,
            "Gamma retains nexus.",
        ),
        MorphologicalLanguagePassage::new(
            "retains-d",
            "retains-source-d",
            4,
            "Delta retains nexus.",
        ),
    ];
    let mut boundary =
        ExactRelationalLanguageEcology::condition_copresent_with_workers(&passages, 4).unwrap();
    let receipt = boundary.execution_receipt();
    assert_eq!(receipt.pending_junctions, 0);
    assert!(boundary.current_passages.is_empty());
    assert!(boundary
        .junction_returns
        .iter()
        .all(|(_, returned)| matches!(
            returned.conduct(),
            ResonanceOccurrenceConduct::Open { .. }
        )));

    // A later occurrence recurs through the retained receptor while every exact candidate
    // retains its own source identity.
    let later = [MorphologicalLanguagePassage::new(
        "retains-e",
        "retains-source-e",
        5,
        "Epsilon retains nexus.",
    )];
    boundary.receive_copresent_with_workers(&later, 4).unwrap();
    let receipt = boundary.execution_receipt();
    assert_eq!(receipt.pending_junctions, 0);
    assert!(
        boundary
            .junction_returns
            .iter()
            .any(|(_, returned)| matches!(
                returned.conduct(),
                ResonanceOccurrenceConduct::Complete { .. }
            )),
        "exact junction returns were {:?}",
        boundary.junction_returns
    );
    let returned_pairs = boundary
        .current_passages
        .iter()
        .map(|(pair, _)| *pair)
        .collect::<LocalSet<_>>();
    assert_eq!(
        returned_pairs,
        LocalSet::from([(0, 4), (1, 4), (2, 4), (3, 4)])
    );
}

#[test]
fn plural_junction_candidates_return_one_to_one_without_a_phase_representative() {
    let passages = vec![
        MorphologicalLanguagePassage::new("a", "source-a", 1, "Alpha retains nexus."),
        MorphologicalLanguagePassage::new("b", "source-b", 2, "Beta retains nexus."),
        MorphologicalLanguagePassage::new("c", "source-c", 3, "Gamma retains nexus."),
        MorphologicalLanguagePassage::new("d", "source-d", 4, "Delta retains nexus."),
    ];
    let boundary =
        ExactRelationalLanguageEcology::condition_copresent_with_workers(&passages, 4).unwrap();
    let (_, phase) = boundary.junction_phases.iter().next().unwrap();
    let action = ActionCurrent::new(Cog::lit(1)).unwrap();
    let mut association = empty_relational_association().unwrap();
    let mut candidates = LocalSequence::new();
    for at in 0..6 {
        candidates.push(
            relational_junction_witness_occurrence(phase, &format!("candidate-{at}"), 10).unwrap(),
        );
    }
    let returned = association
        .receive_configuration(&candidates, action)
        .unwrap();
    assert_eq!(returned.reads().len(), candidates.len());
    assert!(returned
        .reads()
        .iter()
        .zip(&candidates)
        .all(|(read, candidate)| read.occurrence() == candidate.identity()));
    for (read, candidate) in returned.reads().iter().zip(&candidates) {
        let returned_germ = candidate
            .germs()
            .get(1)
            .expect("the relational occurrence declares its returned boundary germ");
        let opposed_germ = candidate
            .germs()
            .first()
            .expect("the relational occurrence declares its opposed boundary germ");
        let required_antecedents = read
            .conduct()
            .required()
            .iter()
            .map(|port| port.antecedent().clone())
            .collect::<LocalSet<_>>();
        assert_eq!(
            required_antecedents,
            LocalSet::from([returned_germ.identity().clone()])
        );
        assert_ne!(returned_germ.identity(), opposed_germ.identity());
    }
}

#[test]
fn refused_swing_remains_one_retryable_causal_front() {
    let first = [MorphologicalLanguagePassage::new(
        "first-retention",
        "first-source",
        1,
        "Alpha retains nexus.",
    )];
    let later = [MorphologicalLanguagePassage::new(
        "second-retention",
        "second-source",
        2,
        "Delta retains nexus.",
    )];
    let mut retried = ExactRelationalLanguageEcology::condition(&first).unwrap();
    let mut refusing = RefusingExecutor;
    assert!(matches!(
        retried.receive_with_executor(&later, 8, &mut refusing),
        Err(RelationalLanguageError::Association(_))
    ));
    let refused = retried.execution_receipt();
    assert_eq!(refused.requested_worker_threads, 8);
    assert_eq!(refused.pending_junctions, 1);
    assert_eq!(refused.open_passages, 1);
    assert_eq!(refused.pending_current_pairs, 0);
    assert_eq!(refused.received_passages, 1);
    assert_eq!(retried.passage_delivery_order("second-retention"), Some(1));
    assert_eq!(
        retried.closed_thought_at_declared_horizon("How do alpha and delta meet?"),
        Err(RelationalLanguageError::OpenPassage)
    );

    let mut host = HostLiveCurrentExecutor;
    assert_eq!(
        retried.receive_with_executor(&later, 8, &mut host).unwrap(),
        1
    );
    let returned = retried.execution_receipt();
    assert_eq!(returned.pending_junctions, 0);
    assert_eq!(returned.open_passages, 0);
    assert_eq!(returned.pending_current_pairs, 0);
    assert_eq!(returned.received_passages, 2);

    let mut uninterrupted = ExactRelationalLanguageEcology::condition(&first).unwrap();
    uninterrupted.receive(&later).unwrap();
    assert_eq!(retried.clauses, uninterrupted.clauses);
    assert_eq!(retried.adjacency, uninterrupted.adjacency);
    assert_eq!(
        retried.association.rest_image().unwrap(),
        uninterrupted.association.rest_image().unwrap()
    );
}

#[test]
fn paired_receiver_current_resumes_the_unreturned_direction_without_new_ids() {
    let passages = [
        MorphologicalLanguagePassage::new(
            "current-left",
            "current-source-left",
            1,
            "Alpha retains nexus.",
        ),
        MorphologicalLanguagePassage::new(
            "current-right",
            "current-source-right",
            2,
            "Sigma carries field.",
        ),
    ];
    let mut ecology = ExactRelationalLanguageEcology::condition(&passages).unwrap();
    assert!(!ecology.current_passages.contains(&(0, 1)));

    let [forward, reverse] = ecology.prepare_current_pair((0, 1)).unwrap();
    let next_after_pair = ecology.next_current_passage;
    ecology
        .receiver_current
        .found_passage(ExactReceiverCurrentPassage {
            id: forward,
            from: clause_site(0).unwrap(),
            to: clause_site(1).unwrap(),
            characteristic_delay: 1,
        })
        .unwrap();
    assert!(ecology.receiver_current.passage(forward).is_some());
    assert!(ecology.receiver_current.passage(reverse).is_none());
    assert_eq!(ecology.pending_current_passages.len(), 1);
    assert_eq!(
        ecology.closed_thought_at_declared_horizon("How do alpha and sigma meet?"),
        Err(RelationalLanguageError::OpenPassage)
    );

    ecology.promote_conducting_pair(0, 1).unwrap();
    assert_eq!(ecology.next_current_passage, next_after_pair);
    assert!(ecology.receiver_current.passage(forward).is_some());
    assert!(ecology.receiver_current.passage(reverse).is_some());
    assert!(ecology.pending_current_passages.is_empty());
    assert_eq!(
        ecology.current_passages.get(&(0, 1)),
        Some(&[forward, reverse])
    );
}

// -------------------------------------------------------------------------------------------------
// The clause-pair characteristic delay, and its orbit.
//
// `characteristic_delay: 1` was pinned at both promotion sites by this ecology — the law's ONLY
// caller — while `ExactReceiverCurrentLaw` accepts any positive `u64`. Every current reading ever
// taken through this organ was therefore taken in one frame, which is `CLAUDE.md` §8's condition
// for a reading that cannot be falsified.
//
// A lifted level that moves nothing is bookkeeping. These tests require the orbit.
// -------------------------------------------------------------------------------------------------

/// One source stating four clauses far apart on its strand, so a separation exists to read.
fn separated_strand() -> Vec<MorphologicalLanguagePassage> {
    vec![MorphologicalLanguagePassage::new(
        "strand",
        "strand-source",
        1,
        "Alpha carries nexus. Beta holds nexus. Gamma retains nexus. Delta preserves nexus.",
    )]
}

#[test]
fn the_uniform_frame_is_the_frame_every_prior_reading_was_taken_in() {
    let ecology = ExactRelationalLanguageEcology::condition(&separated_strand()).unwrap();
    assert_eq!(
        ecology.characteristic_delay_law(),
        ClausePairDelayLaw::Uniform,
        "the default must not move, or every standing reading silently changes frame"
    );
    for passage in ecology.receiver_current.passages() {
        assert_eq!(passage.characteristic_delay, 1);
    }
}

#[test]
fn source_continuity_separates_clause_pairs_the_uniform_frame_superposed() {
    let uniform = ExactRelationalLanguageEcology::condition(&separated_strand()).unwrap();
    let continuity = ExactRelationalLanguageEcology::condition_with_delay_law(
        &separated_strand(),
        1,
        ClausePairDelayLaw::SourceContinuity,
    )
    .unwrap();

    // Same material, same promoted pairs: only the term differs.
    assert_eq!(
        uniform.current_passages.len(),
        continuity.current_passages.len(),
        "changing the delay term must not change WHICH pairs conduct"
    );
    assert!(
        uniform.current_passages.len() > 0,
        "a frame comparison over zero passages is vacuous"
    );

    let uniform_delays: Vec<u64> = uniform
        .receiver_current
        .passages()
        .map(|passage| passage.characteristic_delay)
        .collect();
    let continuity_delays: Vec<u64> = continuity
        .receiver_current
        .passages()
        .map(|passage| passage.characteristic_delay)
        .collect();

    // THE ORBIT. Under the uniform term every passage carries 1, so the frame cannot tell any two
    // pairs apart. Under source continuity the source's own statement order separates them.
    assert!(uniform_delays.iter().all(|delay| *delay == 1));
    assert!(
        continuity_delays.iter().any(|delay| *delay > 1),
        "source continuity returned the uniform frame's delays: the term is inert on this \
         material and the comparison establishes nothing"
    );
    let distinct: BTreeSet<u64> = continuity_delays.iter().copied().collect();
    assert!(
        distinct.len() > 1,
        "the second frame must DISTINGUISH pairs the first superposed, not merely rescale them"
    );
}

#[test]
fn a_pair_crossing_sources_carries_the_extent_of_the_strand_it_leaves() {
    // Across sources there is no separation defined in the material — nothing in either source
    // measures the distance to the other — so the term reads the extent of the strand being left.
    // It is therefore ASYMMETRIC, and the two directions of one pair are computed separately.
    //
    // A cross-source pair is promoted only on an exact object-to-subject contact, so the long
    // strand ends on the short strand's subject.
    let crossing = vec![
        MorphologicalLanguagePassage::new(
            "long",
            "long-source",
            1,
            "Alpha carries beta. Beta holds gamma. Gamma retains delta. Delta preserves epsilon.",
        ),
        MorphologicalLanguagePassage::new("short", "short-source", 2, "Epsilon receives nexus."),
    ];
    let continuity = ExactRelationalLanguageEcology::condition_with_delay_law(
        &crossing,
        1,
        ClausePairDelayLaw::SourceContinuity,
    )
    .unwrap();

    let mut crossed_directions = Vec::new();
    for (pair, _) in continuity.current_passages.iter() {
        let (left, right) = *pair;
        if continuity.clauses[left].source == continuity.clauses[right].source {
            continue;
        }
        crossed_directions.push((
            continuity.pair_characteristic_delay(left, right).unwrap(),
            continuity.pair_characteristic_delay(right, left).unwrap(),
        ));
    }
    assert!(
        !crossed_directions.is_empty(),
        "the fixture founded no cross-source pair, so the asymmetry is untested"
    );
    assert!(
        crossed_directions
            .iter()
            .any(|(forward, reverse)| forward != reverse),
        "leaving a four-clause strand and leaving a one-clause strand must not cost the same; \
         a symmetric return here means the direction was copied rather than computed"
    );
}
