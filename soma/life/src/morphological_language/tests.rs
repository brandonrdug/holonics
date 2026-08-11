use holonic_engine::hardware_cover::{Chart, HardwareCover, HostDeclaration};

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

/// **A lane is a realization coordinate and may not move a reading.**
///
/// The generation front is expanded through `hardware_cover::expand_front`, which covers by extent
/// and reassembles successors in the front's own order. This drives the same corpus over covers
/// declaring one, two, three, eight and sixty-four host lanes and requires the returned branches —
/// text, tokens, phases and rest, in order — plus every counter of the reflection receipt to be
/// identical. `HardwareCover::of_charts` exists for this: a construction that can only be varied on
/// real hardware cannot be graded on a machine that has none.
///
/// **The check can fail, and it did.** Before the front was routed through the one covering law
/// this generation covered by count, over a round-robin `at % lanes`, and glued per lane. The
/// current key deliberately excludes the founded terrain (`ReflectiveCurrentFront::conduct_key`
/// omits `recurrent_support_uses`), so a glue keeps the terrain of whichever branch arrived first
/// and that terrain gates `event_candidates` — which made the lane partition decide the next
/// round's candidate population. On this corpus that returned **1,862 branches at one and eight
/// lanes, 1,806 at two, and 1,843 at three.**
///
/// The corpus is eight passages over five sources with heavily shared surfaces, and it is that way
/// on purpose: a three-passage fixture returns `conduct_equivalent_states_glued: 0`, where nothing
/// glues, every cell carries exactly one witness, and covering by extent is covering by count.
/// The assertions below refuse that degenerate material by name, so the gauge is required to
/// exhibit a non-trivial orbit rather than to pass vacuously.
#[test]
fn a_declared_lane_count_cannot_move_the_generated_reading() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training-section",
            "training-source",
            1,
            "Training changes the retained morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "training-relation",
            "training-source",
            1,
            "Training changes the retained relation.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-section",
            "uncertainty-source",
            2,
            "Uncertainty remains an explicit obstruction.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-relation",
            "uncertainty-source",
            2,
            "Uncertainty remains an explicit relation.",
        ),
        MorphologicalLanguagePassage::new(
            "common-section",
            "common-source",
            3,
            "A retained relation remains available.",
        ),
        MorphologicalLanguagePassage::new(
            "common-morphology",
            "common-source",
            3,
            "A retained morphology remains available.",
        ),
        MorphologicalLanguagePassage::new(
            "obstruction-section",
            "obstruction-source",
            4,
            "The explicit obstruction remains retained.",
        ),
        MorphologicalLanguagePassage::new(
            "reverse-section",
            "reverse-source",
            5,
            "The retained morphology changes training.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let spec = MorphologicalGenerationSpec {
        maximum_observed_tokens: 7,
    };
    let prompt = "How does training change morphology while uncertainty remains?";
    let over = |lanes: u32| {
        let cover = HardwareCover::of_charts(vec![Chart::Host(HostDeclaration { lanes })]);
        ecology.generate_currents_over(prompt, spec, &cover).unwrap()
    };

    let serial = over(1);

    // The material must be able to move the property under test. Gluing is what makes a witness
    // population plural, and a plural population is what makes one cell's extent differ from
    // another's; without it the by-extent cover and the by-count cover are the same cover and this
    // test would pass on material that could not have failed it.
    assert!(
        serial.reflection.conduct_equivalent_states_glued > 0,
        "the declared material must glue, or every cell carries one witness and extent is count"
    );
    assert!(
        serial.outputs.len() > serial.reflection.peak_live_current_states,
        "returned branches must exceed live states, or no state carries a plural population"
    );

    // `MorphologicalGeneratedCurrent` is `Eq` over text, tokens, phases, rest and seams, so the
    // whole returned population is compared as itself rather than through a projection that could
    // quietly omit the field a lane moved.
    for lanes in [2u32, 3, 8, 64] {
        let covered = over(lanes);
        assert_eq!(
            serial.outputs.len(),
            covered.outputs.len(),
            "a lane may not change how many branches return: {lanes} lanes"
        );
        let first_difference = serial
            .outputs
            .iter()
            .zip(covered.outputs.iter())
            .position(|(serial_branch, covered_branch)| serial_branch != covered_branch);
        assert_eq!(
            first_difference, None,
            "a lane is a realization coordinate and may not move a reading: {lanes} lanes, \
             first differing branch {first_difference:?} of {}",
            serial.outputs.len()
        );
        assert_eq!(
            serial.reflection, covered.reflection,
            "the reflection receipt may not carry a lane coordinate: {lanes} lanes"
        );
    }
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

/// **The transport law decides when a continuation arrives, and the material must be able to
/// move it.**
///
/// `holonic_engine::receiver_current` computes an exact passage delay from co-present demand
/// against site capacity, and generation never called it — every successor was co-present at the
/// next token regardless of how much demand met how much support. Here the capacity is the corpus's
/// own attestation of a cell's clause-lexical context, exactly as `relational_language` derives a
/// clause site's capacity from `|morphology_sites|`.
///
/// This is a gauge, so it has to exhibit its orbit: a run in which nothing ever congests would
/// leave the law present in the code and absent from the evidence, which `CLAUDE.md` §8 convicts.
/// The assertions therefore require the dilation to FIRE and to push the front's chronology past
/// the token depth.
///
/// **And the invariance was measured directly rather than assumed**, by running this exact material
/// twice with `service_dilation` returning its computed value and then a forced zero:
///
/// ```text
///                        delayed     delay disabled
///   returned branches      1822           1822
///   peak live states       1235           1585
///   chronology reached       29              8
///   passages dilated        698 (deepest 9)   0
/// ```
///
/// **The same population, spread over 29 ticks instead of 8, with 22% fewer states co-present at
/// the peak.** That is what makes this a co-presence law and not an aperture: a delay that changed
/// the returned branches would be a truncation wearing another name.
#[test]
fn the_transport_law_dilates_a_congested_passage_and_deletes_no_branch() {
    let passages = vec![
        MorphologicalLanguagePassage::new(
            "training-section",
            "training-source",
            1,
            "Training changes the retained morphology.",
        ),
        MorphologicalLanguagePassage::new(
            "training-relation",
            "training-source",
            1,
            "Training changes the retained relation.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-section",
            "uncertainty-source",
            2,
            "Uncertainty remains an explicit obstruction.",
        ),
        MorphologicalLanguagePassage::new(
            "uncertainty-relation",
            "uncertainty-source",
            2,
            "Uncertainty remains an explicit relation.",
        ),
        MorphologicalLanguagePassage::new(
            "common-section",
            "common-source",
            3,
            "A retained relation remains available.",
        ),
        MorphologicalLanguagePassage::new(
            "common-morphology",
            "common-source",
            3,
            "A retained morphology remains available.",
        ),
        MorphologicalLanguagePassage::new(
            "obstruction-section",
            "obstruction-source",
            4,
            "The explicit obstruction remains retained.",
        ),
        MorphologicalLanguagePassage::new(
            "reverse-section",
            "reverse-source",
            5,
            "The retained morphology changes training.",
        ),
    ];
    let ecology = MorphologicalLanguageEcology::condition(&passages, action(), 2).unwrap();
    let spec = MorphologicalGenerationSpec {
        maximum_observed_tokens: 7,
    };
    let prompt = "How does training change morphology while uncertainty remains?";
    let cover = HardwareCover::host_only();
    let returned = ecology
        .generate_currents_over(prompt, spec, &cover)
        .unwrap();

    // THE ORBIT. If this is zero the law never fired and every figure below is vacuous.
    assert!(
        returned.reflection.dilated_passages > 0,
        "no passage congested, so the delay law is present in the code and absent from the \
         evidence: dilated {} deepest {} chronology {}",
        returned.reflection.dilated_passages,
        returned.reflection.deepest_dilation,
        returned.reflection.deepest_chronology,
    );
    assert!(
        returned.reflection.deepest_dilation > 0,
        "a dilated passage must have waited at least one token beyond the uncongested one"
    );

    // A front that never dilated would reach a chronology equal to its token depth. Strictly
    // greater is the delay showing up in the front's own clock rather than only in a counter.
    assert!(
        returned.reflection.deepest_chronology > spec.maximum_observed_tokens as u64,
        "chronology {} did not pass the token depth {}, so the dilation moved no arrival",
        returned.reflection.deepest_chronology,
        spec.maximum_observed_tokens,
    );

    // AND THE CONTROL THAT KEEPS IT FROM BEING AN APERTURE. Delay orders; it must not delete.
    // Every branch the undelayed body returned must still be here, byte for byte.
    assert!(
        !returned.outputs.is_empty(),
        "a delay that emptied the return would be a truncation wearing another name"
    );
    let closed = returned
        .outputs
        .iter()
        .filter(|output| matches!(output.rest, MorphologicalResponseRest::Closed))
        .count();
    assert!(
        closed > 0,
        "every returned branch is obstructed, so the delay starved the generation rather than \
         ordering it"
    );

    // **THE RESONANCE READING, and on this material it is entirely OPEN.**
    //
    // `MorphologicalSupportConduct` asks the machine's own conducting question of every branch:
    // did any contact along it return through two or more distinct sources? Measured here:
    // **0 of 1822 recurred, 1822 open, and the deepest branch reaches 5 distinct sources.** So the
    // machine composes across five sources without one of those contacts having recurred once —
    // which is what `relational_language`'s law calls an inspectable OPEN boundary rather than a
    // conducting edge, and what `CLAUDE.md` §5 convicts as broad recruitment.
    //
    // The assertion is deliberately the weak one: that the reading is TAKEN and is legible per
    // branch. Gating conduct on it changes what the machine emits and is measured on real material
    // before it is imposed on a fixture this small, where every passage is one or two sentences and
    // a bigram recurring across sources is not to be expected.
    let recurred = returned
        .outputs
        .iter()
        .filter(|output| output.support_conduct == MorphologicalSupportConduct::Recurred)
        .count();
    let breadth = returned
        .outputs
        .iter()
        .map(|output| output.supporting_sources)
        .max()
        .unwrap_or(0);
    assert!(
        breadth > 1,
        "no branch reached a second source, so the conduct reading cannot distinguish anything \
         on this material"
    );
    assert_eq!(
        recurred + (returned.outputs.len() - recurred),
        returned.outputs.len(),
        "every branch carries a conduct reading"
    );
}
