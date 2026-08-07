use super::current::{materialize_returned_path_live, receive_question};
use super::*;

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).unwrap()
}

#[test]
fn simultaneous_scales_compose_two_source_phases_and_close_after_both_return() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training-section",
            "training-source",
            1,
            "Training changes the retained morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-section",
            "uncertainty-source",
            2,
            "Uncertainty remains an explicit obstruction.",
        ),
        MorphologicalLanguagePassage::new(
            "common-section",
            "common-source",
            3,
            "A retained relation remains available.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let generation = ecology
        .generate(
            "How does training change morphology while uncertainty remains?",
            MorphologicalGenerationSpec {
                maximum_observed_tokens: 64,
            },
            action(),
            2,
        )
        .unwrap();
    assert_eq!(generation.charge.obligations.len(), 1);
    let required = generation.charge.obligations[0].features.clone();
    assert!(generation.outputs.iter().any(|output| {
        let discharged = output
            .phases
            .iter()
            .filter_map(|phase| phase.discharged_features.get(&0))
            .flat_map(|features| features.iter().cloned())
            .collect::<BTreeSet<_>>();
        output.rest == MorphologicalResponseRest::Closed
            && discharged == required
            && output
                .phases
                .iter()
                .flat_map(|phase| phase.sources.iter().map(String::as_str))
                .collect::<BTreeSet<_>>()
                .len()
                == 2
    }));
}

#[test]
fn returned_event_frontier_forms_a_novel_intra_phase_recurrent_seam() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training",
            "training-source",
            1,
            "Training changes morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty",
            "uncertainty-source",
            2,
            "Changes morphology while uncertainty remains.",
        ),
        MorphologicalLanguagePassage::new(
            "control",
            "control-source",
            3,
            "A separate receiver retains a control.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let generation = ecology
        .generate(
            "Relate training and uncertainty.",
            MorphologicalGenerationSpec {
                maximum_observed_tokens: 32,
            },
            action(),
            2,
        )
        .unwrap();
    let novel = generation
        .outputs
        .iter()
        .find(|output| output.text == "Training changes morphology while uncertainty remains.")
        .expect("the shared suffix seam must remain in the plural frontier");
    assert_eq!(novel.rest, MorphologicalResponseRest::Closed);
    assert_eq!(novel.phases.len(), 1);
    assert_eq!(
        novel.phases[0].sources,
        BTreeSet::from([
            "training-source".to_owned(),
            "uncertainty-source".to_owned()
        ])
    );
    assert!(novel.tokens.iter().enumerate().all(|(at, token)| {
        token.returned_event_count == at + 1
            && (at == 0 || token.transport == MorphologicalTransport::RecurrentLexical)
    }));
    assert!(novel.tokens.iter().any(|token| {
        token.recurrent_context_sources.len() >= 2 && !token.lexical_horizons.is_empty()
    }));
    let inherited = passages
        .iter()
        .map(|passage| lexical_tokens(&passage.text))
        .collect::<Vec<_>>();
    let phase_tokens = novel.tokens[novel.phases[0].emitted_start..novel.phases[0].emitted_end]
        .iter()
        .map(|token| token.token.clone())
        .collect::<Vec<_>>();
    assert!(!inherited.iter().any(|path| {
        path.windows(phase_tokens.len())
            .any(|window| window == phase_tokens)
    }));
}

#[test]
fn plural_terminal_witnesses_return_without_semantic_truncation() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training",
            "training-source",
            1,
            "Training changes morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty",
            "uncertainty-source",
            2,
            "Changes morphology while uncertainty remains.",
        ),
        MorphologicalLanguagePassage::new(
            "control",
            "control-source",
            3,
            "A separate receiver retains a control.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let generation = ecology
        .generate(
            "Relate training and uncertainty.",
            MorphologicalGenerationSpec {
                maximum_observed_tokens: 32,
            },
            action(),
            2,
        )
        .unwrap();

    assert_eq!(generation.reflection.shared_conditioned_bodies, 1);
    assert_eq!(generation.reflection.whole_body_forks, 0);
    assert!(generation.reflection.shared_current_forks > 0);
    assert_eq!(
        generation.reflection.terminal_return_materializations,
        generation.outputs.len()
    );
    assert!(generation
        .outputs
        .iter()
        .all(|output| !output.tokens.is_empty()));
}

#[test]
fn punctuation_cannot_close_an_open_query_fiber() {
    let passages = vec![
        MorphologicalLanguagePassage::new("a", "alpha", 1, "Alpha closes."),
        MorphologicalLanguagePassage::new("b", "beta", 2, "Beta closes."),
        MorphologicalLanguagePassage::new("c", "common", 3, "A common face closes."),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let generated = ecology
        .generate(
            "Relate alpha and beta.",
            MorphologicalGenerationSpec {
                maximum_observed_tokens: 3,
            },
            action(),
            2,
        )
        .unwrap();
    assert!(generated.outputs.iter().all(|output| matches!(
        output.rest,
        MorphologicalResponseRest::ObservationApertureExhausted { .. }
    )));
}

#[test]
fn ordered_region_receiver_rejects_unordered_clause_cooccurrence() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "unordered",
            "unordered-source",
            1,
            "Does a relation make the suffix exact?",
        ),
        MorphologicalLanguagePassage::new(
            "ordered",
            "ordered-source",
            2,
            "The exact suffix frontier conducts.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let charge = ecology
        .charge("Does the exact suffix frontier conduct?")
        .unwrap();
    assert!(charge.obligations.iter().any(|obligation| {
        obligation.local_regions.iter().any(|region| {
            region.ordered_surface
                == ["the", "exact", "suffix", "frontier"]
                    .into_iter()
                    .map(str::to_owned)
                    .collect::<Vec<_>>()
        })
    }));
    assert!(charge.obligations.iter().all(|obligation| {
        obligation
            .local_regions
            .iter()
            .all(|region| region.ordered_surface != ["does", "the", "exact"])
    }));
}

#[test]
fn observation_prefix_cannot_discharge_a_later_ordered_region() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "target",
            "target-source",
            1,
            "Prelude words precede the exact suffix frontier.",
        ),
        MorphologicalLanguagePassage::new(
            "other",
            "other-source",
            2,
            "Another receiver returns separately.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let generation = ecology
        .generate(
            "What is the exact suffix frontier?",
            MorphologicalGenerationSpec {
                maximum_observed_tokens: 2,
            },
            action(),
            2,
        )
        .unwrap();
    assert!(generation.outputs.iter().all(|output| {
        matches!(
            output.rest,
            MorphologicalResponseRest::ObservationApertureExhausted {
                ref open_obligations
            } if !open_obligations.is_empty()
        ) && output.phases.iter().all(|phase| {
            phase.boundary.is_none()
                && phase.discharged_regions.is_empty()
                && phase.discharged_features.is_empty()
        })
    }));
}

#[test]
fn recurring_question_initial_phase_is_conditioned_as_operator_morphology() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training-question",
            "training-source",
            1,
            "How does training change? Training conditions morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-question",
            "uncertainty-source",
            2,
            "How does uncertainty return? Uncertainty remains open.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let charge = ecology
        .charge("How does training condition morphology while uncertainty remains open?")
        .unwrap();
    assert_eq!(
        charge.operator_features,
        ["does", "how"].into_iter().map(str::to_owned).collect()
    );
    let obligated = charge
        .obligations
        .iter()
        .flat_map(|obligation| obligation.features.iter().cloned())
        .collect::<BTreeSet<_>>();
    assert!(!obligated.contains("how"));
    assert!(!obligated.contains("does"));
    assert!(["training", "morphology", "uncertainty"]
        .into_iter()
        .all(|feature| obligated.contains(feature)));
}

#[test]
fn question_operator_recurrence_is_not_forced_to_the_source_file_scale() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training-question",
            "shared-source",
            1,
            "How does training change? Training conditions morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-question",
            "shared-source",
            1,
            "How does uncertainty return? Uncertainty remains open.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let charge = ecology
        .charge("How does training condition morphology while uncertainty remains open?")
        .unwrap();
    assert_eq!(
        charge.operator_features,
        ["does", "how"].into_iter().map(str::to_owned).collect()
    );
    assert!(ecology
        .question_operator_regions()
        .contains(&vec!["how".to_owned(), "does".to_owned()]));
}

#[test]
fn rust_try_glyph_does_not_pose_a_question_to_the_language_ecology() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "first-code",
            "code-source",
            1,
            "let value = machine.receive()?; Can the receiver return?",
        ),
        MorphologicalLanguagePassage::new(
            "second-code",
            "code-source",
            1,
            "let state = machine.rest()?; Can the ecology close?",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let operators = ecology.question_operator_regions();
    assert!(!operators.iter().any(|prefix| {
        prefix
            .first()
            .is_some_and(|surface| surface == "let" || surface == "machine")
    }));
    assert!(operators.contains(&vec!["can".to_owned(), "the".to_owned()]));
}

#[test]
fn one_mounted_return_path_equals_explicit_live_transfer() {
    let prompt = lexical_tokens("What changes?");
    let generated = ["Training", "changes", "morphology", "."];
    let transferred = materialize_returned_path_live(
        receive_question(&prompt, action(), 2).unwrap(),
        &prompt,
        generated.iter().copied(),
        action(),
        2,
    )
    .unwrap();

    let mut tokenwise = receive_question(&prompt, action(), 2).unwrap();
    let mut predecessor = prompt.last().cloned().unwrap();
    for (at, token) in generated.iter().enumerate() {
        let germs = token_germs(&[predecessor, (*token).to_owned()]).unwrap();
        let occurrence =
            ResonanceOccurrence::self_emanated(u64::try_from(at + 1).unwrap(), germs).unwrap();
        let mut executor = ParallelHostLiveCurrentExecutor::new(2);
        tokenwise
            .receive_with(&occurrence, action(), &mut executor)
            .unwrap();
        predecessor = (*token).to_owned();
    }
    assert_eq!(transferred, tokenwise.rest_image().unwrap());
}
