//! Receiver-indexed next-front defects without a scalar winner.

use holonic_engine::phoenix::runtime::RuntimeReceipt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::cohort::SiblingHistoryCut;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixedBodyIdentity {
    pub schema: String,
    pub product_sha256: String,
    pub predecessor_sha256: String,
    pub morphology_sha256: String,
    pub codec_sha256: String,
    pub runtime_law_sha256: String,
    pub presentation_law_sha256: String,
    pub complete_identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActivityCuts {
    pub residency_sha256: String,
    pub realization_path_sha256: String,
    pub receiver_causal_sha256: String,
    pub apparatus_sha256: String,
    pub cuts_are_separate: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordedSiblingFace {
    pub occurrence: String,
    pub first_native_id: u32,
    pub first_surface: String,
    pub complete_native_ids: Vec<u32>,
    pub terminal_interval: (i64, i64),
    pub first_front_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShortestSeparator {
    pub receiver: String,
    pub history_depth: usize,
    pub consequence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateFace {
    pub native_id: u32,
    pub surface: String,
    pub lower: i64,
    pub upper: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateDefect {
    pub occurrence: String,
    pub candidate: CandidateFace,
    pub candidate_and_sibling_are_one_occurrence: bool,
    pub native_id_agrees: bool,
    pub surface_agrees: bool,
    pub intervals_intersect: bool,
    pub candidate_contains_terminal_top_lower: bool,
    pub sibling_contains_terminal_top_lower: bool,
    pub shortest_separator: Option<ShortestSeparator>,
    pub open_successor_fibres: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DefectHigherCell {
    pub occurrence: String,
    pub common_face: i64,
    pub candidate_occurrences: Vec<String>,
    pub sibling_incident: bool,
    pub interpretation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistoryDefectReturn {
    pub schema: String,
    pub history_cut_occurrence: String,
    pub history_sha256: String,
    pub history_messages: usize,
    pub presentation: String,
    pub runtime_receipt_artifact: String,
    pub runtime_receipt_sha256: String,
    pub productive_code_closure: String,
    pub runtime_input_sha256: String,
    pub fixed_body: FixedBodyIdentity,
    pub frozen_members_verified: bool,
    pub source_access_forbidden_population: usize,
    pub activity: ActivityCuts,
    pub generated_candidate_population: usize,
    pub separated_vocabulary_population: usize,
    pub recorded_sibling: RecordedSiblingFace,
    pub recorded_sibling_in_candidate_fibre: bool,
    pub defects: Vec<CandidateDefect>,
    pub unresolved_higher_cell: DefectHigherCell,
    pub tool_world_pair_population: u64,
    pub later_operator_return_present: bool,
    pub open_fibres: Vec<String>,
    pub scalar_winner_selected: bool,
    pub probability_substituted_for_causal_return: bool,
    pub provider_priority_rule: bool,
    pub truth_status: String,
}

pub fn fixed_body(receipt: &RuntimeReceipt) -> Result<FixedBodyIdentity, String> {
    let runtime_law_sha256 = digest_json(&receipt.runtime_law)?;
    let complete_identity_sha256 = digest_json(&(
        &receipt.product_identity,
        &receipt.predecessor_identity,
        &receipt.morphology_identity,
        &receipt.codec_companion_identities,
        &receipt.runtime_law,
        &receipt.input.presentation.law_sha256,
        &receipt.reconstruction_identity,
        &receipt.codec_identity,
    ))?;
    Ok(FixedBodyIdentity {
        schema: "holonics.athena-a2-fixed-body.v1".to_owned(),
        product_sha256: receipt.product_identity.sha256.clone(),
        predecessor_sha256: receipt.predecessor_identity.sha256.clone(),
        morphology_sha256: receipt.morphology_identity.sha256.clone(),
        codec_sha256: receipt.codec_identity.clone(),
        runtime_law_sha256,
        presentation_law_sha256: receipt.input.presentation.law_sha256.clone(),
        complete_identity_sha256,
    })
}

pub fn activity_cuts(receipt: &RuntimeReceipt) -> Result<ActivityCuts, String> {
    Ok(ActivityCuts {
        residency_sha256: digest_json(&(
            &receipt.tower_admission,
            &receipt.streamed,
            &receipt.apparatus_census.resident_before,
            &receipt.apparatus_census.resident_after,
        ))?,
        realization_path_sha256: digest_json(&(
            &receipt.product_identity,
            &receipt.predecessor_identity,
            &receipt.morphology_identity,
            &receipt.codec_companion_identities,
            &receipt.overlay_execution,
        ))?,
        receiver_causal_sha256: digest_json(&(
            &receipt.input,
            &receipt.generated,
            &receipt.total_work,
            &receipt.overlay_work,
        ))?,
        apparatus_sha256: digest_json(&(
            &receipt.apparatus_census,
            &receipt.apparatus_prediction,
            &receipt.execution,
        ))?,
        cuts_are_separate: true,
    })
}

pub fn analyze(
    cut: &SiblingHistoryCut,
    presentation: &str,
    runtime_receipt_artifact: String,
    runtime_receipt_sha256: String,
    productive_code_closure: String,
    receipt: &RuntimeReceipt,
    sibling_ids: Vec<u32>,
    sibling_surface: String,
    sibling_interval: (i64, i64),
) -> Result<HistoryDefectReturn, String> {
    let first_native_id = *sibling_ids
        .first()
        .ok_or_else(|| "the exterior sibling crossed to no native codewords".to_owned())?;
    let body = fixed_body(receipt)?;
    let activity = activity_cuts(receipt)?;
    let sibling_in = receipt
        .generated
        .plural
        .iter()
        .any(|candidate| candidate.native_id == first_native_id);
    let sibling_contains_top = contains(sibling_interval, receipt.generated.top_lower);
    let mut defects = Vec::with_capacity(receipt.generated.plural.len());
    let mut higher_members = Vec::with_capacity(receipt.generated.plural.len());
    for candidate in &receipt.generated.plural {
        let occurrence = addressed(&[
            b"athena-a2-candidate-defect/v1",
            cut.occurrence.as_bytes(),
            presentation.as_bytes(),
            &candidate.native_id.to_le_bytes(),
        ]);
        higher_members.push(occurrence.clone());
        let native_id_agrees = candidate.native_id == first_native_id;
        let surface_agrees = candidate.surface == sibling_surface;
        let intervals_intersect =
            candidate.lower <= sibling_interval.1 && sibling_interval.0 <= candidate.upper;
        let shortest_separator = if !native_id_agrees {
            Some(ShortestSeparator {
                receiver: "terminal native-codeword face".to_owned(),
                history_depth: cut.history.len(),
                consequence: format!(
                    "candidate native {} differs from exterior sibling native {}",
                    candidate.native_id, first_native_id
                ),
            })
        } else if !surface_agrees {
            Some(ShortestSeparator {
                receiver: "authenticated exterior-codec surface".to_owned(),
                history_depth: cut.history.len(),
                consequence: "one native address reopened under the surface receiver".to_owned(),
            })
        } else {
            None
        };
        defects.push(CandidateDefect {
            occurrence,
            candidate: CandidateFace {
                native_id: candidate.native_id,
                surface: candidate.surface.clone(),
                lower: candidate.lower,
                upper: candidate.upper,
            },
            candidate_and_sibling_are_one_occurrence: false,
            native_id_agrees,
            surface_agrees,
            intervals_intersect,
            candidate_contains_terminal_top_lower: contains(
                (candidate.lower, candidate.upper),
                receipt.generated.top_lower,
            ),
            sibling_contains_terminal_top_lower: sibling_contains_top,
            shortest_separator,
            open_successor_fibres: vec![
                "the addressed input partition retains every source token row, byte boundary and straddling token in its reconstruction fibre"
                    .to_owned(),
                "the next-token receiver does not determine the complete emitted response"
                    .to_owned(),
                "candidate tool/world consequence is not enacted in A2".to_owned(),
                "equal first codeword would not identify causal occurrence or later conduct"
                    .to_owned(),
            ],
        });
    }
    let tool_world_pair_population = cut
        .world
        .claude_tool_returns
        .pair_population
        .saturating_add(cut.world.codex_tool_returns.pair_population);
    let open_fibres = vec![
        "every addressed message row may reopen to its complete source-token and byte-boundary reconstruction fibre"
            .to_owned(),
        "all response suffixes after the returned next-token front".to_owned(),
        "Athena candidate world consequences remain un-enacted; recorded sibling world returns are retained separately".to_owned(),
        "private teacher interiors are unavailable and were not invented".to_owned(),
    ];
    Ok(HistoryDefectReturn {
        schema: "holonics.athena-a2-history-defect-return.v1".to_owned(),
        history_cut_occurrence: cut.occurrence.clone(),
        history_sha256: cut.native_history_sha256.clone(),
        history_messages: cut.history.len(),
        presentation: presentation.to_owned(),
        runtime_receipt_artifact,
        runtime_receipt_sha256,
        productive_code_closure,
        runtime_input_sha256: receipt.input.text_sha256.clone(),
        fixed_body: body,
        frozen_members_verified: receipt.frozen_members_verified,
        source_access_forbidden_population: receipt.source_access.forbidden.len(),
        activity,
        generated_candidate_population: receipt.generated.plural.len(),
        separated_vocabulary_population: receipt.generated.separated,
        recorded_sibling: RecordedSiblingFace {
            occurrence: cut.sibling.occurrence.clone(),
            first_native_id,
            first_surface: sibling_surface,
            complete_native_ids: sibling_ids,
            terminal_interval: sibling_interval,
            first_front_only: true,
        },
        recorded_sibling_in_candidate_fibre: sibling_in,
        defects,
        unresolved_higher_cell: DefectHigherCell {
            occurrence: addressed(&[
                b"athena-a2-interval-nerve-cell/v1",
                cut.occurrence.as_bytes(),
                presentation.as_bytes(),
                &receipt.generated.top_lower.to_le_bytes(),
            ]),
            common_face: receipt.generated.top_lower,
            candidate_occurrences: higher_members,
            sibling_incident: sibling_contains_top,
            interpretation: "every retained candidate interval contains the maximal lower face; this is one inhabited unresolved nerve cell, not a tie broken by a score".to_owned(),
        },
        tool_world_pair_population,
        later_operator_return_present: cut.world.later_operator_return.is_some(),
        open_fibres,
        scalar_winner_selected: false,
        probability_substituted_for_causal_return: false,
        provider_priority_rule: false,
        truth_status: "established-bounded".to_owned(),
    })
}

fn contains(interval: (i64, i64), point: i64) -> bool {
    interval.0 <= point && point <= interval.1
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| hex(&Sha256::digest(bytes)))
        .map_err(|error| error.to_string())
}

fn addressed(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    hex(&digest.finalize())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}
