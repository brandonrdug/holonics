use super::*;

/// Return a complete Lean-owned formal face through the one reflective runtime continuation.
/// Kernel population counts and diagnostics remain observer testimony; only actual generated
/// theorem/declaration source faces enter the codec receiver.
pub(super) fn receive(
    body: &mut AgenticLanguageEcology,
    returned: &AgenticFormalReturn,
) -> Result<AgenticFormalReturnReceipt, AgenticLanguageError> {
    if body.open.is_some() || body.standing.turn != AgenticTurnStanding::Rest {
        return Err(AgenticLanguageError::QuestionAlreadyOpen);
    }
    let completion = &returned.completion;
    let diagnosis = completion.diagnosis();
    let target_episode_identity = completion.target_episode();
    let target_witnesses = diagnosis.target_lineage();
    if returned.identity.trim().is_empty()
        || !completion.validates_formal_return_face()
        || completion.deed().trim().is_empty()
        || diagnosis.target_episode() != target_episode_identity
        || target_witnesses.is_empty()
        || body.codec_program_versions().any(|version| {
            version.returned_by == returned.identity
                || version.identity == format!("formal-return-codec/{}", completion.deed())
        })
    {
        return Err(AgenticLanguageError::EmptyFeedback);
    }

    let target_episode = body
        .episodes
        .iter()
        .find(|episode| episode.identity == target_episode_identity)
        .ok_or_else(|| {
            AgenticLanguageError::UnknownFeedbackTarget(target_episode_identity.to_owned())
        })?;
    if target_episode.role != AgenticDialogueRole::EmanatedAnswer {
        return Err(AgenticLanguageError::FeedbackTargetIsNotDialogueOutput(
            target_episode_identity.to_owned(),
        ));
    }
    let target_lineage = body.answer_lineages.get(target_episode_identity);
    let input = target_codec_face(target_episode, target_lineage);
    if !target_witnesses
        .iter()
        .all(|witness| input.lineage.contains(witness))
    {
        return Err(AgenticLanguageError::EmptyFeedback);
    }

    let mut ordered_regions = BTreeSet::new();
    for source in completion.kernel_admitted_sources() {
        let region = lexical_tokens(&source.source);
        if region.is_empty() {
            return Err(AgenticLanguageError::EmptyFeedback);
        }
        ordered_regions.insert(region);
    }
    if ordered_regions.is_empty() {
        return Err(AgenticLanguageError::EmptyFeedback);
    }

    let fiber = completion.returned();
    let mut output_lineage = input.lineage.to_owned();
    output_lineage.insert(returned.identity.to_owned());
    output_lineage.insert(completion.deed().to_owned());
    output_lineage.insert(target_episode_identity.to_owned());
    output_lineage.extend(target_witnesses.iter().cloned());
    output_lineage.extend(diagnosis.passage_witnesses().iter().cloned());
    output_lineage.insert(fiber.theorem_face_sha256.to_owned());
    output_lineage.insert(fiber.generated_source_identity.to_owned());
    for source in completion.kernel_admitted_sources() {
        output_lineage.insert(source.identity.clone());
        output_lineage.insert(source.source_sha256.clone());
        output_lineage.insert(source.proof_sha256.clone());
    }
    let output = AgenticLanguageCodecFace {
        identity: format!("{}/face", returned.identity),
        receiver: returned.receiver,
        ordered_regions,
        lineage: output_lineage,
    };
    let mut input_only_regions = input.ordered_regions.to_owned();
    input_only_regions.retain(|region| !output.ordered_regions.contains(region));
    let mut output_only_regions = output.ordered_regions.to_owned();
    output_only_regions.retain(|region| !input.ordered_regions.contains(region));
    let active_transductions = body.codec_training()?.active_template_count();
    let cultivation = AgenticLanguageCodecCultivation {
        generation: body.codec_training()?.generation,
        receiver_views: 0,
        prior_relations: Default::default(),
        observed_fibers: Default::default(),
        active_transductions_before: active_transductions,
        active_transductions_after: active_transductions,
    };
    let parents = target_lineage
        .map(|lineage| lineage.codec_versions.to_owned())
        .unwrap_or_else(|| target_episode.codec_versions.to_owned());
    let version = AgenticLanguageCodecVersion {
        identity: format!("formal-return-codec/{}", completion.deed()),
        aperture: AgenticLanguageCodecAperture::FormalReturn,
        parents,
        input,
        output,
        output_episode: target_episode_identity.to_owned(),
        returned_by: returned.identity.to_owned(),
        residual: AgenticLanguageCodecResidual {
            input_only_regions,
            output_only_regions,
        },
        cultivation,
    };
    let reflective_codec_versions = body
        .standing
        .reflective_codec_versions
        .checked_add(1)
        .ok_or(AgenticLanguageError::CarrierExtent)?;
    let reflective_codec_commits = body
        .standing
        .reflective_codec_commits
        .checked_add(1)
        .ok_or(AgenticLanguageError::CarrierExtent)?;
    let codec_versions_before = body.codec_program_versions().count();
    let before = body
        .codec_runtime
        .continuation(body.codec_continuation)
        .ok_or(AgenticLanguageError::CarrierExtent)?;
    let continuation = before.id.0;
    let codec_before = before.codec.0;
    let instruction_before = before.next_instruction;
    let running_before = before.state == ContinuationState::Running;
    if !running_before {
        return Err(AgenticLanguageError::CarrierExtent);
    }

    let version = body.commit_reflective_codec(version, None)?;
    body.standing.reflective_codec_versions = reflective_codec_versions;
    body.standing.reflective_codec_commits = reflective_codec_commits;
    body.standing.active_codec_transductions = active_transductions;
    let after = body
        .codec_runtime
        .continuation(body.codec_continuation)
        .expect("the reflective continuation cannot disappear after its own committed return");
    Ok(AgenticFormalReturnReceipt {
        identity: returned.identity.to_owned(),
        deed: completion.deed().to_owned(),
        theorem: fiber.theorem.to_owned(),
        codec_version: version.identity,
        codec_versions_before,
        codec_versions_after: body.codec_program_versions().count(),
        continuation: AgenticReflectiveContinuationReceipt {
            continuation,
            codec_before,
            codec_after: after.codec.0,
            instruction_before,
            instruction_after: after.next_instruction,
            running_before,
            running_after: after.state == ContinuationState::Running,
        },
    })
}
