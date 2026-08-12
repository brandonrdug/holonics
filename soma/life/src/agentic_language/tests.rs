use super::*;
use body::num::Cog;

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).unwrap()
}

fn body() -> AgenticLanguageEcology {
    let capabilities = vec![AgenticLanguageCapability::new("repository-search", 70)];
    let trajectories = vec![
            AgenticLanguageTrajectory::new(
                "suffix",
                1,
                "What did the suffix correction establish?",
                "repository-search",
                vec![MorphologicalLanguagePassage::new(
                    "suffix-observation",
                    "suffix-record",
                    11,
                    "The suffix current advances through returned events.",
                )],
                "The correction made the returned event advance the suffix current used by the next emanation.",
            ),
            AgenticLanguageTrajectory::new(
                "phase",
                2,
                "What did the phase correction establish?",
                "repository-search",
                vec![MorphologicalLanguagePassage::new(
                    "phase-observation",
                    "phase-record",
                    12,
                    "The phase receiver retains quotient and causal carry.",
                )],
                "The correction retained phase quotient and carry instead of one scalar cell.",
            ),
        ];
    AgenticLanguageEcology::condition(
        &[MorphologicalLanguagePassage::new(
            "language-form",
            "language-form",
            3,
            "A correction changes the current used by a later passage.",
        )],
        &capabilities,
        &trajectories,
        AgenticLanguageSpec::default(),
        action(),
        2,
    )
    .unwrap()
}

fn answer_with_return(
    body: &mut AgenticLanguageEcology,
    identity: &str,
    prompt: &str,
    observation: &str,
) -> AgenticLanguageAnswer {
    let question = AgenticLanguageQuestion::new(identity, 90, prompt);
    match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(deed) => match body
            .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(
                &AgenticLanguageWorldReturn::new(
                    deed.identity,
                    vec![MorphologicalLanguagePassage::new(
                        format!("{identity}/observation"),
                        format!("{identity}/source"),
                        91,
                        observation,
                    )],
                ),
            ))
            .unwrap()
        {
            AgenticLanguageConsequence::Answer(answer) => answer,
            other => panic!("world return must answer, received {other:?}"),
        },
        other => panic!("question must answer or emit a deed, received {other:?}"),
    }
}

#[test]
fn mounted_open_boundary_emits_a_deed_without_fabricating_an_answer_trajectory() {
    let mut body = AgenticLanguageEcology::condition(
        &[MorphologicalLanguagePassage::new(
            "conditioned-language-body",
            "conditioned-language-body",
            3,
            "A returned difference changes the contemporary body used by a later passage.",
        )],
        &[AgenticLanguageCapability::new("research-world", 70).with_open_boundary()],
        &[],
        AgenticLanguageSpec::default(),
        action(),
        2,
    )
    .unwrap();
    let question = AgenticLanguageQuestion::new(
        "open-research-question",
        90,
        "Which body carries the returned difference?",
    );
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => {
            panic!("an ungrounded question must emit the mounted deed, received {other:?}")
        }
    };
    assert_eq!(deed.capability.identity, "research-world");
    assert!(deed.inherited_routes.is_empty());
    assert!(!deed.arguments.is_empty());
    assert!(deed.argument_surface().contains("body"));
    assert!(matches!(
        body.standing().turn,
        AgenticTurnStanding::AwaitingWorldReturn { .. }
    ));
    let expected = body.rest_receipt().unwrap();
    let remounted = body.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(remounted.rest_receipt().unwrap(), expected);
}

#[test]
fn world_may_act_only_after_deed_and_return_founds_a_local_episode() {
    let mut body = body();
    let question = AgenticLanguageQuestion::new(
        "reflection-question",
        90,
        "What did the reflection correction establish?",
    );
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        AgenticLanguageConsequence::Answer(_) => panic!("unseen reflection was not grounded"),
        _ => panic!("unseen reflection must emit the learned deed"),
    };
    assert_eq!(deed.capability.identity, "repository-search");
    assert_eq!(body.standing().base_body_reconditions, 0);
    let open_expected = body.rest_receipt().unwrap();
    let mut body = body.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(body.rest_receipt().unwrap(), open_expected);
    let returned = AgenticLanguageWorldReturn::new(
            deed.identity.clone(),
            vec![
                MorphologicalLanguagePassage::new(
                    "reflection-observation-a",
                    "reflection-record",
                    91,
                    "The reflection correction makes the returned current change the local morphology used by the next passage.",
                ),
                MorphologicalLanguagePassage::new(
                    "reflection-observation-b",
                    "reflection-record",
                    91,
                    "It carries one shared body and sparse exact current states.",
                ),
            ],
        );
    let answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(_) => panic!("a return cannot emit the same deed"),
        _ => panic!("a world return must emit its answer"),
    };
    assert!(!answer.text.is_empty());
    assert_eq!(answer.world_deed.as_deref(), Some(deed.identity.as_str()));
    assert!(answer.evidence_sources.contains("reflection-record"));
    assert_eq!(body.standing().base_body_reconditions, 0);
    assert_eq!(body.standing().locally_conditioned_episode_organs, 3);
}

#[test]
fn related_later_question_conducts_without_replaying_the_world_deed() {
    let mut body = body();
    let first = AgenticLanguageQuestion::new(
        "reflection-question",
        90,
        "What did the reflection correction establish?",
    );
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&first))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        _ => panic!("first question must emit a deed"),
    };
    let returned = AgenticLanguageWorldReturn::new(
            deed.identity,
            vec![MorphologicalLanguagePassage::new(
                "reflection-observation",
                "reflection-record",
                91,
                "The reflection correction makes the returned current change the local morphology used by the next passage.",
            )],
        );
    body.receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
        .unwrap();
    let deeds_before = body.standing().emitted_deeds;
    let later = AgenticLanguageQuestion::new(
        "later-question",
        90,
        "What does the returned current change in the next passage?",
    );
    let answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&later))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(_) => {
            panic!("the returned reflection must alter later conduct")
        }
        _ => panic!("the grounded follow-up must answer"),
    };
    assert!(answer.world_deed.is_none());
    assert_eq!(body.standing().emitted_deeds, deeds_before);
    assert_eq!(body.standing().base_body_reconditions, 0);
    assert_eq!(body.episode_origin_census(), (2, 1, 2));
}

#[test]
fn a_new_unknown_direct_face_is_not_erased_by_prior_dialogue_context() {
    let mut body = body();
    let first = AgenticLanguageQuestion::new(
        "reflection-question",
        90,
        "What did the reflection correction establish?",
    );
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&first))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("first question must emit a deed, received {other:?}"),
    };
    body.receive_occurrence(AgenticLanguageOccurrence::WorldReturn(
        &AgenticLanguageWorldReturn::new(
            deed.identity,
            vec![MorphologicalLanguagePassage::new(
                "reflection-observation",
                "reflection-record",
                91,
                "The reflection correction changes the local morphology.",
            )],
        ),
    ))
    .unwrap();

    let unknown = AgenticLanguageQuestion::new("unknown-question", 90, "What is photosynthesis?");
    let consequence = body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&unknown))
        .unwrap();
    assert!(!matches!(
        consequence,
        AgenticLanguageConsequence::Answer(_)
    ));
}

#[test]
fn joined_relation_current_realizes_source_absent_wording_and_retains_both_witnesses() {
    let mut body = body();
    let question = AgenticLanguageQuestion::new(
        "composite-question",
        90,
        "How does one returned token change the exact suffix current used by the next emanation?",
    );
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        AgenticLanguageConsequence::Answer(_) => {
            panic!("unseen composite question must emit a deed")
        }
        _ => panic!("unseen composite question must emit the learned deed"),
    };
    let returned = AgenticLanguageWorldReturn::new(
            deed.identity.clone(),
            vec![MorphologicalLanguagePassage::new(
                "joined-reflection-return",
                "reflection-record",
                91,
                "One returned token advances those exact suffix currents. The next emanation is formed from the advanced currents themselves.",
            )],
        );
    let answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(_) => panic!("returned evidence must answer"),
        _ => panic!("returned evidence must answer"),
    };
    assert_eq!(
            answer.text,
            "Those exact suffix currents are advanced by one returned token. The advanced currents themselves form the next emanation."
        );
    assert!(answer.novel_contiguous_surface);
    assert!(answer.generated.caused_seams.is_empty());
    assert_eq!(answer.generated.phases.len(), 2);
    assert!(answer
        .generated
        .tokens
        .iter()
        .all(|token| { token.transport == MorphologicalTransport::RelationalRealization }));
    let thought = answer
        .relational_thought
        .as_ref()
        .expect("the outward wording must retain its causing relation body");
    assert_eq!(thought.clauses.len(), 2);
    assert_eq!(thought.joins.len(), 1);
    assert!(!thought.selected().unwrap().inherited_contiguous);
    assert!(answer.closure.closed_by_returned_obligations);
    assert!(!deed.arguments.is_empty());
    assert!(!deed.argument_surface().is_empty());
}

#[test]
fn incomparable_closed_relation_currents_remain_beside_one_terminal_return() {
    let mut body = body();
    let question =
        AgenticLanguageQuestion::new("plural-proof-question", 90, "Who checks the proof?");
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("unseen proof question must emit a deed, received {other:?}"),
    };
    let returned = AgenticLanguageWorldReturn::new(
        deed.identity,
        vec![
            MorphologicalLanguagePassage::new(
                "first-proof-return",
                "first-proof-source",
                91,
                "The first verifier checks the proof.",
            ),
            MorphologicalLanguagePassage::new(
                "second-proof-return",
                "second-proof-source",
                92,
                "The second verifier checks the proof.",
            ),
        ],
    );
    let answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("plural proof returns must answer, received {other:?}"),
    };

    assert_eq!(answer.relational_thoughts.len(), 1, "{}", answer.text);
    assert!(answer.relational_thought.is_some());
    assert_eq!(answer.selection.inclusion_maximal_population, 2);
    assert_eq!(answer.selection.retained_alternative_population, 1);
    assert_eq!(answer.retained_alternatives.len(), 1);
    assert_eq!(answer.generated.phases.len(), 1);
    assert!(answer.text.contains("first verifier"), "{}", answer.text);
    assert!(!answer.text.contains("second verifier"), "{}", answer.text);
    assert!(answer.retained_alternatives[0]
        .generated
        .tokens
        .iter()
        .any(|token| token.token == "second"));
    assert!(answer.closure.closed_by_returned_obligations);
}

#[test]
fn correction_obstructs_the_addressed_answer_and_conditions_later_conduct() {
    let mut body = body();
    let first_question =
        AgenticLanguageQuestion::new("stop-question", 90, "How does the response close?");
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&first_question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("expected deed, received {other:?}"),
    };
    let returned = AgenticLanguageWorldReturn::new(
        deed.identity,
        vec![MorphologicalLanguagePassage::new(
            "old-stop",
            "old-stop-source",
            91,
            "The response closes when the observer aperture is reached.",
        )],
    );
    let first_answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("expected answer, received {other:?}"),
    };
    let reified_before = body
        .reify_answer_codec_face(&first_answer.answer_episode_identity)
        .unwrap();
    let correction = AgenticLanguageFeedback::new(
        "stop-correction",
        90,
        first_answer.answer_episode_identity.clone(),
        AgenticLanguageFeedbackKind::Correction,
        "The response closes when every query obligation returns at a caused sentence boundary.",
    );
    let receipt = match body
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&correction))
        .unwrap()
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt,
        other => panic!("correction must return a receipt, received {other:?}"),
    };
    let committed = receipt
        .committed_codec_version
        .as_ref()
        .expect("a correction must commit an operative codec version");
    assert_eq!(committed.input, reified_before);
    assert_eq!(body.codec_versions(), vec![committed]);
    assert!(receipt
        .obstructed_episodes
        .contains(&first_answer.answer_episode_identity));
    let revised_question = AgenticLanguageQuestion::new(
        "revised-stop-followup",
        90,
        "The response closes when what returns at a caused sentence boundary?",
    );
    let revised = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&revised_question))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("corrected body must answer, received {other:?}"),
    };
    assert!(revised.text.contains("every query obligation"));
    assert!(revised
        .evidence_sources
        .contains("dialogue/stop-correction"));
    assert!(revised
        .operative_codec_versions
        .contains(&committed.identity));
    assert_eq!(body.standing().received_corrections, 1);
    assert_eq!(body.standing().reflective_codec_versions, 1);
    assert_eq!(body.standing().reflective_codec_commits, 1);
    let expected = body.rest_receipt().unwrap();
    let remounted = body.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(remounted.rest_receipt().unwrap(), expected);
}

#[test]
fn native_rest_transfers_the_complete_agent_without_replaying_history() {
    let body = body();
    let expected = body.rest_receipt().unwrap();
    let relational_clauses = body.relational_body().clauses().len();
    let native = body.into_native_rest().unwrap();
    let remounted = native.remount().unwrap();
    assert_eq!(remounted.rest_receipt().unwrap(), expected);
    assert_eq!(
        remounted.relational_body().clauses().len(),
        relational_clauses
    );
}

#[test]
fn reified_codec_carries_an_old_input_face_into_a_disjoint_returned_output() {
    let mut body = body();
    let first_question =
        AgenticLanguageQuestion::new("closure-question", 90, "How does the response close?");
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&first_question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("expected deed, received {other:?}"),
    };
    let first_answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(
            &AgenticLanguageWorldReturn::new(
                deed.identity,
                vec![MorphologicalLanguagePassage::new(
                    "legacy-closure",
                    "legacy-closure-source",
                    91,
                    "The response closes when the observer aperture is reached.",
                )],
            ),
        ))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("expected answer, received {other:?}"),
    };
    let feedback = AgenticLanguageFeedback::new(
            "closure-codec-return",
            90,
            first_answer.answer_episode_identity,
            AgenticLanguageFeedbackKind::Correction,
            "Completion follows only after every query obligation returns at a caused sentence boundary.",
        );
    let committed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&feedback))
        .unwrap()
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt
            .committed_codec_version
            .expect("the correction must install a codec"),
        other => panic!("expected codec commit, received {other:?}"),
    };
    let revised = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &AgenticLanguageQuestion::new("closure-revised", 90, "How does the response close?"),
        ))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("reflective codec must answer, received {other:?}"),
    };
    assert!(!revised.text.trim().is_empty());
    assert!(revised
        .operative_codec_versions
        .contains(&committed.identity));
    assert_eq!(body.active_codec_versions(), vec![&committed]);
    let expected = body.rest_receipt().unwrap();
    let remounted = body.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(remounted.rest_receipt().unwrap(), expected);
}

#[test]
fn correction_of_a_codec_carried_answer_founds_a_lineaged_successor() {
    let mut body = body();
    let question = AgenticLanguageQuestion::new(
        "lineaged-closure-question",
        90,
        "How does the response close?",
    );
    let deed = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("expected deed, received {other:?}"),
    };
    let inherited_answer = match body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(
            &AgenticLanguageWorldReturn::new(
                deed.identity,
                vec![MorphologicalLanguagePassage::new(
                    "lineaged-legacy-closure",
                    "lineaged-legacy-source",
                    91,
                    "The response closes when the observer aperture is reached.",
                )],
            ),
        ))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("expected answer, received {other:?}"),
    };
    let first_return = AgenticLanguageFeedback::new(
        "first-codec-return",
        90,
        inherited_answer.answer_episode_identity,
        AgenticLanguageFeedbackKind::Correction,
        "Completion follows after every query obligation returns at a caused sentence boundary.",
    );
    let first_codec = match body
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&first_return))
        .unwrap()
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt
            .committed_codec_version
            .expect("first correction must install a codec"),
        other => panic!("expected first codec commit, received {other:?}"),
    };
    let first_revision = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &AgenticLanguageQuestion::new(
                "first-codec-question",
                90,
                "How does the response close?",
            ),
        ))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("first codec must answer, received {other:?}"),
    };
    assert!(first_revision
        .operative_codec_versions
        .contains(&first_codec.identity));

    let second_return = AgenticLanguageFeedback::new(
        "second-codec-return",
        90,
        first_revision.answer_episode_identity,
        AgenticLanguageFeedbackKind::Correction,
        "Closure is certified only when every local obligation and its returned boundary agree.",
    );
    let second_codec = match body
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&second_return))
        .unwrap()
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt
            .committed_codec_version
            .expect("second correction must install a successor codec"),
        other => panic!("expected successor codec commit, received {other:?}"),
    };
    assert_ne!(second_codec.identity, first_codec.identity);
    assert_eq!(
        second_codec.parents,
        BTreeSet::from([first_codec.identity.clone()])
    );
    assert_eq!(body.codec_versions().len(), 2);
    assert_eq!(body.codec_versions()[0], &first_codec);
    assert_eq!(body.codec_versions()[1], &second_codec);

    let second_revision = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &AgenticLanguageQuestion::new(
                "second-codec-question",
                90,
                "How does the response close?",
            ),
        ))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("successor codec must answer, received {other:?}"),
    };
    assert!(!second_revision.text.trim().is_empty());
    assert!(second_revision
        .operative_codec_versions
        .contains(&first_codec.identity));
    assert!(second_revision
        .operative_codec_versions
        .contains(&second_codec.identity));
    let expected = body.rest_receipt().unwrap();
    assert_eq!(expected.codec_versions.len(), 2);
    let remounted = body.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(remounted.rest_receipt().unwrap(), expected);
}

#[test]
fn two_returned_corrections_cultivate_a_novel_third_language_face() {
    let mut body = body();
    let ada = answer_with_return(
        &mut body,
        "ada-question",
        "Can the suffix receiver return Ada?",
        "The suffix receiver can return Ada.",
    );
    let first = AgenticLanguageFeedback::new(
        "ada-correction",
        90,
        ada.answer_episode_identity,
        AgenticLanguageFeedbackKind::Correction,
        "The suffix receiver can return Ada.",
    );
    let first_version = match body
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&first))
        .unwrap()
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt
            .committed_codec_version
            .expect("first correction must commit a version"),
        other => panic!("first correction returned {other:?}"),
    };
    assert!(first_version.cultivation.receiver_views > 0);
    assert_eq!(first_version.cultivation.active_transductions_before, 0);
    assert_eq!(first_version.cultivation.active_transductions_after, 0);
    let lin = answer_with_return(
        &mut body,
        "lin-question",
        "Can the suffix receiver return Lin?",
        "The suffix receiver can return Lin.",
    );
    let second = AgenticLanguageFeedback::new(
        "lin-correction",
        90,
        lin.answer_episode_identity,
        AgenticLanguageFeedbackKind::Correction,
        "The suffix receiver can return Lin.",
    );
    let second_version = match body
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&second))
        .unwrap()
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt
            .committed_codec_version
            .expect("second correction must commit a version"),
        other => panic!("second correction returned {other:?}"),
    };
    assert_eq!(
        second_version.cultivation.receiver_views,
        first_version.cultivation.receiver_views
    );
    assert_eq!(second_version.cultivation.active_transductions_before, 0);
    assert!(second_version.cultivation.active_transductions_after > 0);
    assert_eq!(body.standing().reflective_codec_training_events, 2);
    assert_eq!(
        body.standing().active_codec_transductions,
        second_version.cultivation.active_transductions_after
    );

    let mira_question =
        AgenticLanguageQuestion::new("mira-question", 90, "Can the suffix receiver return Mira?");
    let mira = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&mira_question))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("the recurrent codec must answer, received {other:?}"),
    };
    assert_eq!(mira.text, "The suffix receiver can return Mira.");
    assert!(mira.world_deed.is_none());
    assert!(mira.novel_contiguous_surface);
    assert!(mira.cultivated_codec_paths.len() >= 2);
    assert!(mira
        .cultivated_codec_paths
        .iter()
        .all(|path| path.recurrence >= CODEC_MINIMUM_RECURRENCE));
    assert!(mira.cultivated_codec_paths.iter().all(|path| {
        path.version_lineage.contains(&first_version.identity)
            && path.version_lineage.contains(&second_version.identity)
    }));

    let native = body.codec_training_native_bytes().unwrap();
    let remounted_training = TrainingEcology::decode_native_bytes(&native).unwrap();
    assert_eq!(remounted_training.encode_native_bytes().unwrap(), native);
    let noor_views =
        codec_training_views(&lexical_tokens("Can the suffix receiver return Noor?")).unwrap();
    assert!(noor_views.iter().any(|view| {
        remounted_training
            .predict_exact(&view.faces, &view.parameters)
            .unwrap()
            .consequences()
            .contains(b"The suffix receiver can return Noor.".as_slice())
    }));

    let expected = body.rest_receipt().unwrap();
    assert_eq!(expected.codec_training, native);
    let mut remounted = body.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(remounted.rest_receipt().unwrap(), expected);
    let sol = match remounted
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &AgenticLanguageQuestion::new(
                "sol-question",
                90,
                "Can the suffix receiver return Sol?",
            ),
        ))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("remounted recurrent codec must answer, received {other:?}"),
    };
    assert_eq!(sol.text, "The suffix receiver can return Sol.");
    assert!(!sol.cultivated_codec_paths.is_empty());
}

#[test]
fn unresolved_action_relation_returns_a_readable_clarification() {
    let capabilities = vec![
        AgenticLanguageCapability::new("repository-search", 70),
        AgenticLanguageCapability::new("file-change", 71),
    ];
    let trajectories = vec![
        AgenticLanguageTrajectory::new(
            "repository-route",
            1,
            "How should repository evidence return?",
            "repository-search",
            vec![MorphologicalLanguagePassage::new(
                "repository-observation",
                "repository-source",
                11,
                "Repository evidence returns through a typed search deed.",
            )],
            "Search the repository and return exact evidence.",
        ),
        AgenticLanguageTrajectory::new(
            "file-route",
            2,
            "How should a file change return?",
            "file-change",
            vec![MorphologicalLanguagePassage::new(
                "file-observation",
                "file-source",
                12,
                "A file change returns through an exact write deed.",
            )],
            "Change the file and return its exact receipt.",
        ),
    ];
    let mut body = AgenticLanguageEcology::condition(
        &[MorphologicalLanguagePassage::new(
            "clarification-form",
            "clarification-form",
            3,
            "An unresolved action relation asks which caused path should carry it.",
        )],
        &capabilities,
        &trajectories,
        AgenticLanguageSpec::default(),
        action(),
        2,
    )
    .unwrap();
    let ambiguous =
        AgenticLanguageQuestion::new("ambiguous-question", 90, "How should the return proceed?");
    let clarification = match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&ambiguous))
        .unwrap()
    {
        AgenticLanguageConsequence::Clarification(clarification) => clarification,
        other => panic!("ambiguity must clarify, received {other:?}"),
    };
    assert_eq!(clarification.alternatives.len(), 2);
    assert!(clarification.text.contains("Which caused path"));
    assert!(matches!(
        body.standing().turn,
        AgenticTurnStanding::AwaitingClarification { .. }
    ));
    let refinement =
        AgenticLanguageQuestion::new("repository-refinement", 90, "Use repository evidence.");
    match body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&refinement))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => {
            assert_eq!(deed.capability.identity, "repository-search");
            assert!(deed.argument_surface().contains("repository"));
        }
        other => panic!("refinement must select the repository deed, received {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------------
// The non-consuming fork.
//
// `into_native_rest` consumes the body, so before `rest_image` existed a counterfactual arm had no
// control to run against: the second body could only be had by destroying the first. These four
// tests establish that the fork exists, that it is exact, that it is *non*-consuming, and that the
// two arms it yields are causally independent.
// -------------------------------------------------------------------------------------------------

#[test]
fn a_rest_image_remounts_an_exact_second_body_without_consuming_the_first() {
    let mut cultivated = body();
    answer_with_return(
        &mut cultivated,
        "suffix-question",
        "What did the suffix correction establish?",
        "The returned event advances the suffix current.",
    );
    let image = cultivated.rest_image().unwrap();
    assert_eq!(image.history().len(), cultivated.history().len());
    assert!(
        !image.history().is_empty(),
        "the image must carry the causes, not merely the standing"
    );

    let remounted = image
        .remount()
        .expect("the declared causes reproduce the body");
    assert_eq!(
        remounted.rest_receipt().unwrap(),
        cultivated.rest_receipt().unwrap(),
        "a replayed body must be receipt-identical to the one imaged"
    );

    // Non-consuming: the original still conducts, and taking the image did not move its standing.
    let after = cultivated.rest_receipt().unwrap();
    assert_eq!(&after, image.receipt());
}

#[test]
fn the_two_arms_of_a_fork_diverge_only_by_what_each_received() {
    let mut cultivated = body();
    answer_with_return(
        &mut cultivated,
        "suffix-question",
        "What did the suffix correction establish?",
        "The returned event advances the suffix current.",
    );
    let image = cultivated.rest_image().unwrap();

    let held = image.remount().unwrap();
    let mut moved = image.remount().unwrap();
    assert_eq!(
        held.rest_receipt().unwrap(),
        moved.rest_receipt().unwrap(),
        "two arms of one fork begin identical"
    );

    // One arm receives a further cause; the other receives nothing.
    answer_with_return(
        &mut moved,
        "phase-question",
        "What did the phase correction establish?",
        "The phase receiver retained quotient and carry.",
    );
    assert_ne!(
        held.rest_receipt().unwrap(),
        moved.rest_receipt().unwrap(),
        "the arm that received a cause must depart from the arm that did not"
    );
    assert_eq!(
        held.rest_receipt().unwrap(),
        *image.receipt(),
        "the untouched arm must not have moved: the two arms are causally independent"
    );
}

#[test]
fn a_refused_occurrence_founds_no_cause_and_therefore_no_history() {
    let mut cultivated = body();
    let before = cultivated.history().len();
    // A world return naming a deed that was never emitted is refused; refusing must retain nothing,
    // or the replay would found standing the imaged body never had.
    let orphan = AgenticLanguageWorldReturn::new(
        "deed/never-emitted",
        vec![MorphologicalLanguagePassage::new(
            "orphan-observation",
            "orphan-source",
            93,
            "A section returned for a deed the body never emitted.",
        )],
    );
    assert!(cultivated
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&orphan))
        .is_err());
    assert_eq!(
        cultivated.history().len(),
        before,
        "a refused occurrence caused no standing and must leave no cause behind"
    );
    assert!(cultivated.rest_image().unwrap().remount_equal().unwrap());
}

#[test]
fn remount_refuses_a_body_its_declared_causes_do_not_reproduce() {
    // The falsifier, exercised rather than asserted: strike a cause out of an otherwise exact
    // image and require the remount to REFUSE, naming the mismatch. Absent this control the
    // equality above could hold for a `remount` that never compared anything.
    let mut cultivated = body();
    answer_with_return(
        &mut cultivated,
        "suffix-question",
        "What did the suffix correction establish?",
        "The returned event advances the suffix current.",
    );
    let image = cultivated.rest_image().unwrap();
    assert!(image.remount_equal().unwrap());

    let ablated = image.with_history_prefix(0);
    assert!(
        ablated.history().is_empty(),
        "the ablated image declares no causes"
    );
    assert!(
        matches!(
            ablated.remount(),
            Err(AgenticLanguageError::RestRemountMismatch)
        ),
        "an image whose causes do not reproduce its receipt must refuse to remount"
    );
    let (departed, reproduced) = ablated.remount_departed().unwrap();
    assert!(!reproduced);
    assert_ne!(
        departed.rest_receipt().unwrap(),
        *ablated.receipt(),
        "the departed body is returned so the departure can be read, not only reported"
    );
}

/// One caller-retained executor which counts what it was asked to realize and forwards every
/// request to exactly the host carrier the private path would have built.
struct CountingHostExecutor {
    host: ParallelHostLiveCurrentExecutor,
    enactments: usize,
}

impl LiveCurrentExecutor for CountingHostExecutor {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &soma_membrane::SparseStandingSurface,
        currents: &[soma_membrane::CurrentExecutionRequest<'_>],
        relations: &[soma_membrane::DirectedExecutionRequest],
        regional: &[soma_membrane::RegionalExecutionRequest<'_>],
    ) -> Result<soma_membrane::ExecutedContemporaryEvent, soma_membrane::LiveCurrentError> {
        self.enactments += 1;
        self.host
            .enact(physical_revision, standing, currents, relations, regional)
    }
}

/// One caller-retained executor which refuses every enactment.
struct RefusingExecutor {
    consulted: usize,
}

impl LiveCurrentExecutor for RefusingExecutor {
    fn enact(
        &mut self,
        _physical_revision: u64,
        _standing: &soma_membrane::SparseStandingSurface,
        _currents: &[soma_membrane::CurrentExecutionRequest<'_>],
        _relations: &[soma_membrane::DirectedExecutionRequest],
        _regional: &[soma_membrane::RegionalExecutionRequest<'_>],
    ) -> Result<soma_membrane::ExecutedContemporaryEvent, soma_membrane::LiveCurrentError> {
        self.consulted += 1;
        Err(soma_membrane::LiveCurrentError::PhysicalSettlement)
    }
}

/// A caller-mounted carrier reaches the agentic answer, not only agentic conditioning.
///
/// Equality of the returned answer alone would not separate a real twin from one which took the
/// argument and quietly rebuilt its own host pool. Two frames make it falsifiable: the supplied
/// executor is the only executor either answer path may reach, so a nonzero count proves it
/// carried the answer; and a *refusing* carrier must make the answer fail, which no fake twin can
/// reproduce because it never consults the argument at all.
#[test]
fn a_mounted_carrier_reaches_both_agentic_answer_paths() {
    const DEED_QUESTION: &str = "What did the reflection correction establish?";
    const GROUNDED_QUESTION: &str = "What does the returned current change in the next passage?";
    const OBSERVATION: &str = "The reflection correction makes the returned current change the local morphology used by the next passage.";

    fn world_return(deed: String) -> AgenticLanguageWorldReturn {
        AgenticLanguageWorldReturn::new(
            deed,
            vec![MorphologicalLanguagePassage::new(
                "reflection-observation",
                "reflection-record",
                91,
                OBSERVATION,
            )],
        )
    }

    // The private-host path, which is what every caller had before the answer seam was joined.
    let mut private_body = body();
    let question = AgenticLanguageQuestion::new("reflection-question", 90, DEED_QUESTION);
    let AgenticLanguageConsequence::Deed(deed) = private_body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    else {
        panic!("the unseen question must emit a deed");
    };
    let AgenticLanguageConsequence::Answer(private_world) = private_body
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&world_return(
            deed.identity,
        )))
        .unwrap()
    else {
        panic!("the world return must answer");
    };
    let later = AgenticLanguageQuestion::new("later-question", 90, GROUNDED_QUESTION);
    let AgenticLanguageConsequence::Answer(private_grounded) = private_body
        .receive_occurrence(AgenticLanguageOccurrence::Question(&later))
        .unwrap()
    else {
        panic!("the grounded follow-up must answer");
    };

    // The same cycle through one supplied carrier, counted between occurrences.
    let mut counted_body = body();
    let mut counting = CountingHostExecutor {
        host: ParallelHostLiveCurrentExecutor::new(2),
        enactments: 0,
    };
    let AgenticLanguageConsequence::Deed(deed) = counted_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&question),
            &mut counting,
        )
        .unwrap()
    else {
        panic!("the unseen question must emit a deed");
    };
    // Deed emission crosses no Swing event; the carrier is carried unused to the world return.
    assert_eq!(counting.enactments, 0);
    let AgenticLanguageConsequence::Answer(counted_world) = counted_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::WorldReturn(&world_return(deed.identity)),
            &mut counting,
        )
        .unwrap()
    else {
        panic!("the world return must answer");
    };
    let after_world_return = counting.enactments;
    let AgenticLanguageConsequence::Answer(counted_grounded) = counted_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&later),
            &mut counting,
        )
        .unwrap()
    else {
        panic!("the grounded follow-up must answer");
    };

    assert_eq!(private_world, counted_world);
    assert_eq!(private_grounded, counted_grounded);
    assert!(
        after_world_return > 0,
        "the world-return answer must cross the supplied carrier"
    );
    assert!(
        counting.enactments > after_world_return,
        "the locally-grounded answer must cross the supplied carrier too"
    );

    // The refusal, on both answer paths. A fake twin never consults the argument, so it answers.
    let mut refused_world_body = body();
    let mut refusing = RefusingExecutor { consulted: 0 };
    let AgenticLanguageConsequence::Deed(deed) = refused_world_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&question),
            &mut refusing,
        )
        .unwrap()
    else {
        panic!("the unseen question must emit a deed");
    };
    assert!(matches!(
        refused_world_body.receive_occurrence_with_executor(
            AgenticLanguageOccurrence::WorldReturn(&world_return(deed.identity)),
            &mut refusing,
        ),
        Err(AgenticLanguageError::Morphology(_))
    ));
    assert!(
        refusing.consulted > 0,
        "the refusal control is vacuous unless the carrier was reached"
    );

    let mut refused_grounded_body = body();
    let mut working = CountingHostExecutor {
        host: ParallelHostLiveCurrentExecutor::new(2),
        enactments: 0,
    };
    let AgenticLanguageConsequence::Deed(deed) = refused_grounded_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&question),
            &mut working,
        )
        .unwrap()
    else {
        panic!("the unseen question must emit a deed");
    };
    refused_grounded_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::WorldReturn(&world_return(deed.identity)),
            &mut working,
        )
        .unwrap();
    let mut refusing_grounded = RefusingExecutor { consulted: 0 };
    assert!(matches!(
        refused_grounded_body.receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&later),
            &mut refusing_grounded,
        ),
        Err(AgenticLanguageError::Morphology(_))
    ));
    assert!(
        refusing_grounded.consulted > 0,
        "the refusal control is vacuous unless the carrier was reached"
    );
}
