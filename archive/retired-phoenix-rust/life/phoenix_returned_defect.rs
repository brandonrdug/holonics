//! Sealed history-only candidates and genuinely later sibling returns.
//!
//! A candidate is the complete plural terminal potential returned by the inherited organ. It is
//! content-addressed before the sibling source can cross the process boundary. The later return is
//! a graded two-legged defect; subtraction is not presumed outside an additive receiver.

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    exact_work::ExactWork,
    phoenix::{
        runtime::{ProductSession, RuntimeReturn},
        streamed::{InterventionSite, ReceiverOption},
        tower::Intervention,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::exchange_world_tube::ContinuationWorldWindow;

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixCandidateHistoryFace {
    pub occurrence: String,
    pub speaker: String,
    pub text: String,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixCandidateRequest {
    pub proposal: String,
    pub history_text: String,
    pub byte_boundaries: Vec<usize>,
    pub history_faces: Vec<PhoenixCandidateHistoryFace>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixCandidateAlternative {
    pub native_id: u32,
    pub surface: String,
    pub lower: i64,
    pub upper: i64,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixSealedCandidate {
    pub schema: String,
    pub proposal: String,
    pub occurrence: String,
    pub history_sha256: String,
    pub history_occurrences: Vec<String>,
    pub history_incidence_sha256: String,
    pub presented_text_sha256: String,
    pub product_identity: String,
    pub predecessor_identity: String,
    pub morphology_identity: String,
    pub input_reconstruction_sha256: String,
    pub terminal_position: usize,
    pub terminal_potential_sha256: String,
    pub terminal_potential: Vec<(i64, i64)>,
    pub alternatives: Vec<PhoenixCandidateAlternative>,
    pub separated_alternative_population: usize,
    pub sibling_material_mounted: bool,
    pub source_access_forbidden: Vec<String>,
    pub resident: PhoenixCandidateResidentReceipt,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixCandidateResidentReceipt {
    pub schema: String,
    pub device: String,
    pub mode: String,
    pub kernel_sha256: String,
    pub tower_deed_launches: u64,
    pub total_deed_launches: u64,
    pub terminal_synchronizations: u64,
    pub memory_at_mount_free: u64,
    pub memory_at_mount_total: u64,
    pub memory_at_return_free: u64,
    pub memory_at_return_total: u64,
    pub exact_work: ExactWork,
    pub cpu_semantic_replay_after_device: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperatorReturnTestimony {
    pub occurrence: String,
    pub text: String,
    pub text_sha256: String,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixSiblingTestimony {
    pub proposal: String,
    pub response_occurrences: Vec<String>,
    pub response_text: String,
    pub response_sha256: String,
    pub world_consequence: ContinuationWorldWindow,
    pub later_operator_return: Option<OperatorReturnTestimony>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DefectGrain {
    TerminalCodeword,
    ResponseBoundary,
    WholeResponse,
    WorldConsequence,
    OperatorReturn,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DefectRelation {
    Equal,
    CandidateFibreContainsSibling,
    Separated,
    OpenCandidateExterior,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradedDefectFace {
    pub grain: DefectGrain,
    pub candidate_face: String,
    pub sibling_face: String,
    pub relation: DefectRelation,
    pub resident_candidate_class: u32,
    pub resident_sibling_class: u32,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidentDefectReceipt {
    pub schema: String,
    pub device: String,
    pub block_threads: u32,
    pub warp_size: u32,
    pub launches: u64,
    pub receiver_grains: usize,
    pub terminal_fibre_population: usize,
    pub terminal_sibling_class: u32,
    pub terminal_sibling_in_candidate_fibre: bool,
    pub cpu_semantic_replay_after_device: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhoenixReturnedSiblingDefect {
    pub schema: String,
    pub proposal: String,
    pub candidate_occurrence: String,
    pub sibling_occurrence: String,
    pub common_history_boundary_sha256: String,
    pub target_native_ids: Vec<u32>,
    pub target_first_surface: String,
    pub target_first_interval: Option<(i64, i64)>,
    pub candidate_alternative_fibre_sha256: String,
    pub candidate_alternative_population: usize,
    pub candidate_maximal_population: usize,
    pub graded_faces: Vec<GradedDefectFace>,
    pub resident: ResidentDefectReceipt,
    pub sibling_revealed_after_candidate_seal: bool,
    pub additive_residual_assumed: bool,
    pub open_fibres: Vec<String>,
}

pub fn conduct_phoenix_history_candidate(
    session: &ProductSession,
    request: &PhoenixCandidateRequest,
) -> Result<PhoenixSealedCandidate, String> {
    let reconstructed = request
        .history_faces
        .iter()
        .map(|face| format!("{}\n", face.text))
        .collect::<String>();
    if request.history_text.is_empty()
        || request.byte_boundaries.first() != Some(&0)
        || request.byte_boundaries.last() != Some(&request.history_text.len())
        || request.byte_boundaries.len() != request.history_faces.len() + 1
        || reconstructed != request.history_text
        || request.history_faces.is_empty()
        || request
            .history_faces
            .iter()
            .any(|face| !matches!(face.speaker.as_str(), "user" | "assistant"))
    {
        return Err("the candidate request is not one complete addressed history".to_owned());
    }
    let faces = request
        .history_faces
        .iter()
        .map(|face| (face.speaker.as_str(), face.text.as_str()))
        .collect::<Vec<_>>();
    let presented = session.present_exterior_exchange(&faces)?;
    let returned = session.infer_with_intervention(
        &presented.text,
        InterventionSite::Nowhere,
        &Intervention::None,
        ReceiverOption::Terminal,
    )?;
    seal(request, &presented.text_sha256, &returned)
}

fn seal(
    request: &PhoenixCandidateRequest,
    presented_text_sha256: &str,
    returned: &RuntimeReturn,
) -> Result<PhoenixSealedCandidate, String> {
    if returned.receipt.input.text_sha256 != presented_text_sha256
        || returned.receipt.source_access.forbidden.len() > 0
        || returned.receipt.generated.plural.is_empty()
        || returned.cultivated.cultivated_potential.len()
            != returned.receipt.generated.vocabulary_extent
        || returned.receipt.generated.plural.len() + returned.receipt.generated.separated
            != returned.receipt.generated.vocabulary_extent
        || !returned.receipt.execution.device_name.contains("NVIDIA")
        || returned.receipt.execution.terminal_synchronizations == 0
        || returned.receipt.apparatus_census.tower_deed_launches == 0
    {
        return Err(
            "history-only candidate return failed its source or plural-future audit".to_owned(),
        );
    }
    let alternatives = returned
        .receipt
        .generated
        .plural
        .iter()
        .map(|candidate| PhoenixCandidateAlternative {
            native_id: candidate.native_id,
            surface: candidate.surface.clone(),
            lower: candidate.lower,
            upper: candidate.upper,
        })
        .collect::<Vec<_>>();
    let terminal_potential_sha256 = digest_intervals(&returned.cultivated.cultivated_potential);
    let history_incidence_sha256 = sha(&serde_json::to_vec(&(
        &request.byte_boundaries,
        request
            .history_faces
            .iter()
            .map(|face| (&face.occurrence, &face.speaker))
            .collect::<Vec<_>>(),
    ))
    .map_err(|error| error.to_string())?);
    let draft = serde_json::to_vec(&(
        &request.proposal,
        &history_incidence_sha256,
        &returned.receipt.product_identity.sha256,
        &returned.receipt.predecessor_identity.sha256,
        &returned.receipt.morphology_identity.sha256,
        &returned.receipt.input.presentation.reconstruction_sha256,
        &terminal_potential_sha256,
        &alternatives,
    ))
    .map_err(|error| error.to_string())?;
    Ok(PhoenixSealedCandidate {
        schema: "soma-life.phoenix-sealed-history-candidate.v1".to_owned(),
        proposal: request.proposal.clone(),
        occurrence: sha(&draft),
        history_sha256: sha(request.history_text.as_bytes()),
        history_occurrences: request
            .history_faces
            .iter()
            .map(|face| face.occurrence.clone())
            .collect(),
        history_incidence_sha256,
        presented_text_sha256: presented_text_sha256.to_owned(),
        product_identity: returned.receipt.product_identity.sha256.clone(),
        predecessor_identity: returned.receipt.predecessor_identity.sha256.clone(),
        morphology_identity: returned.receipt.morphology_identity.sha256.clone(),
        input_reconstruction_sha256: returned
            .receipt
            .input
            .presentation
            .reconstruction_sha256
            .clone(),
        terminal_position: returned.receipt.generated.terminal_position,
        terminal_potential_sha256,
        terminal_potential: returned.cultivated.cultivated_potential.clone(),
        alternatives,
        separated_alternative_population: returned.receipt.generated.separated,
        sibling_material_mounted: false,
        source_access_forbidden: returned.receipt.source_access.forbidden.clone(),
        resident: PhoenixCandidateResidentReceipt {
            schema: "holonic-engine.phoenix-candidate-resident-return.v1".to_owned(),
            device: returned.receipt.execution.device_name.clone(),
            mode: returned.receipt.execution.mode.clone(),
            kernel_sha256: returned.receipt.execution.kernel_sha256.clone(),
            tower_deed_launches: returned.receipt.apparatus_census.tower_deed_launches,
            total_deed_launches: returned.receipt.apparatus_census.total_deed_launches,
            terminal_synchronizations: returned.receipt.execution.terminal_synchronizations,
            memory_at_mount_free: returned.receipt.execution.memory_at_mount_free,
            memory_at_mount_total: returned.receipt.execution.memory_at_mount_total,
            memory_at_return_free: returned.receipt.execution.memory_at_return_free,
            memory_at_return_total: returned.receipt.execution.memory_at_return_total,
            exact_work: returned.receipt.total_work.clone(),
            cpu_semantic_replay_after_device: false,
        },
    })
}

pub fn return_sibling_defect(
    session: &ProductSession,
    card: &mut CudaRefineExecutor,
    candidate: &PhoenixSealedCandidate,
    sibling: &PhoenixSiblingTestimony,
) -> Result<PhoenixReturnedSiblingDefect, String> {
    if candidate.proposal != sibling.proposal
        || candidate.sibling_material_mounted
        || sibling.response_text.is_empty()
        || sha(sibling.response_text.as_bytes()) != sibling.response_sha256
        || sibling
            .later_operator_return
            .as_ref()
            .is_some_and(|returned| sha(returned.text.as_bytes()) != returned.text_sha256)
    {
        return Err("the candidate and later sibling do not share one sealed boundary".to_owned());
    }
    let target_native_ids = session.encode(&sibling.response_text)?;
    let target = *target_native_ids
        .first()
        .ok_or("the later sibling encoded to no native occurrence")?;
    let target_first_surface = session
        .predecessor()
        .codebook()
        .native_surface(target)
        .map_err(|error| error.to_string())?
        .to_owned();
    let before_launches = card.launches();
    let (terminal_sibling_class, terminal_sibling_in_candidate_fibre) =
        terminal_fibre_relation(card, &candidate.alternatives, target)?;
    let target_first_interval = terminal_sibling_in_candidate_fibre
        .then(|| {
            candidate
                .alternatives
                .iter()
                .find(|alternative| alternative.native_id == target)
                .map(|alternative| (alternative.lower, alternative.upper))
        })
        .flatten();
    let candidate_fibre = serde_json::to_vec(&(
        &candidate.terminal_potential,
        &candidate.alternatives,
        candidate.separated_alternative_population,
    ))
    .map_err(|error| error.to_string())?;
    let candidate_alternative_fibre_sha256 = sha(&candidate_fibre);
    let codeword_relation = if terminal_sibling_in_candidate_fibre {
        DefectRelation::CandidateFibreContainsSibling
    } else {
        DefectRelation::Separated
    };
    let candidate_codeword_face = sha(&candidate
        .alternatives
        .iter()
        .flat_map(|alternative| alternative.native_id.to_le_bytes())
        .collect::<Vec<_>>());
    let world_consequence_sha256 =
        sha(&serde_json::to_vec(&sibling.world_consequence).map_err(|error| error.to_string())?);
    let sibling_occurrence = sha(&serde_json::to_vec(&(
        &sibling.proposal,
        &sibling.response_occurrences,
        &sibling.response_sha256,
        &sibling.world_consequence,
        &sibling.later_operator_return,
    ))
    .map_err(|error| error.to_string())?);
    let face_material = [
        (
            DefectGrain::TerminalCodeword,
            candidate_codeword_face,
            target.to_string(),
            codeword_relation,
        ),
        (
            DefectGrain::ResponseBoundary,
            "one-open-emanative-frontier".to_owned(),
            sibling.response_occurrences.len().to_string(),
            DefectRelation::OpenCandidateExterior,
        ),
        (
            DefectGrain::WholeResponse,
            candidate.terminal_potential_sha256.clone(),
            sibling.response_sha256.clone(),
            DefectRelation::OpenCandidateExterior,
        ),
        (
            DefectGrain::WorldConsequence,
            "not-yet-enacted".to_owned(),
            world_consequence_sha256,
            DefectRelation::OpenCandidateExterior,
        ),
        (
            DefectGrain::OperatorReturn,
            "not-yet-returned".to_owned(),
            sibling
                .later_operator_return
                .as_ref()
                .map(|returned| returned.text_sha256.clone())
                .unwrap_or_else(|| "open-exterior".to_owned()),
            DefectRelation::OpenCandidateExterior,
        ),
    ];
    let receiver_grains = face_material.len();
    let mut graded_faces = Vec::with_capacity(receiver_grains);
    for (grain, candidate_face, sibling_face, relation) in face_material {
        let (resident_candidate_class, resident_sibling_class) = resident_pair_classes(
            card,
            grain,
            candidate_face.as_bytes(),
            sibling_face.as_bytes(),
        )?;
        graded_faces.push(GradedDefectFace {
            grain,
            candidate_face,
            sibling_face,
            relation,
            resident_candidate_class,
            resident_sibling_class,
        });
    }
    let launches = card.launches() - before_launches;
    if launches == 0 || !card.device_name().contains("NVIDIA") {
        return Err("the graded defect did not return from the resident card".to_owned());
    }
    Ok(PhoenixReturnedSiblingDefect {
        schema: "soma-life.phoenix-returned-sibling-defect.v1".to_owned(),
        proposal: candidate.proposal.clone(),
        candidate_occurrence: candidate.occurrence.clone(),
        sibling_occurrence,
        common_history_boundary_sha256: candidate.history_sha256.clone(),
        target_native_ids,
        target_first_surface,
        target_first_interval,
        candidate_alternative_fibre_sha256,
        candidate_alternative_population: candidate.terminal_potential.len(),
        candidate_maximal_population: candidate.alternatives.len(),
        graded_faces,
        resident: ResidentDefectReceipt {
            schema: "holonic-engine.phoenix-resident-graded-defect.v1".to_owned(),
            device: card.device_name().to_owned(),
            block_threads: card.block_threads(),
            warp_size: card.warp_size(),
            launches,
            receiver_grains,
            terminal_fibre_population: candidate.terminal_potential.len(),
            terminal_sibling_class,
            terminal_sibling_in_candidate_fibre,
            cpu_semantic_replay_after_device: false,
        },
        sibling_revealed_after_candidate_seal: true,
        additive_residual_assumed: false,
        open_fibres: vec![
            "the candidate remains plural until a later receiver founds a selection".to_owned(),
            "whole-response, world and operator faces remain open after one emanative frontier"
                .to_owned(),
        ],
    })
}

fn terminal_fibre_relation(
    card: &mut CudaRefineExecutor,
    alternatives: &[PhoenixCandidateAlternative],
    target: u32,
) -> Result<(u32, bool), String> {
    let mut keys = alternatives
        .iter()
        .map(|alternative| u64::from(alternative.native_id))
        .collect::<Vec<_>>();
    keys.push(u64::from(target));
    let classes = vec![1u32; keys.len()];
    let quotient = card
        .quotient_on_device(&classes, &keys)
        .map_err(|error| error.to_string())?;
    let target_class = *quotient
        .cell_class
        .last()
        .ok_or("the resident terminal fibre returned no sibling cell")?;
    let contains = quotient.cell_class[..alternatives.len()].contains(&target_class);
    Ok((target_class, contains))
}

fn resident_pair_classes(
    card: &mut CudaRefineExecutor,
    grain: DefectGrain,
    candidate: &[u8],
    sibling: &[u8],
) -> Result<(u32, u32), String> {
    let mut classes = vec![1u32, 1u32];
    let lengths = [candidate.len() as u64, sibling.len() as u64];
    classes = card
        .quotient_on_device(&classes, &lengths)
        .map_err(|error| error.to_string())?
        .cell_class;
    let words = candidate.len().max(sibling.len()).div_ceil(8);
    for at in 0..words {
        let keys = [
            tagged_word(grain, candidate, at),
            tagged_word(grain, sibling, at),
        ];
        classes = card
            .quotient_on_device(&classes, &keys)
            .map_err(|error| error.to_string())?
            .cell_class;
    }
    Ok((classes[0], classes[1]))
}

fn tagged_word(grain: DefectGrain, face: &[u8], at: usize) -> u64 {
    let mut word = [0u8; 8];
    let from = at * word.len();
    let until = (from + word.len()).min(face.len());
    if from < until {
        word[..until - from].copy_from_slice(&face[from..until]);
    }
    if at == 0 {
        word[0] ^= grain as u8;
    }
    u64::from_le_bytes(word)
}

fn digest_intervals(intervals: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"phoenix/sealed-terminal-potential/v1");
    for (lower, upper) in intervals {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    hex(digest.finalize().as_slice())
}

fn sha(octets: &[u8]) -> String {
    hex(Sha256::digest(octets).as_slice())
}

fn hex(octets: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(octets.len() * 2);
    for octet in octets {
        out.push(DIGITS[(octet >> 4) as usize] as char);
        out.push(DIGITS[(octet & 15) as usize] as char);
    }
    out
}
