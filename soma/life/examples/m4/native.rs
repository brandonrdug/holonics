//! Recover one nontrivial M3 leader from the addressed reconstruction evidence.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use holonic_engine::generator_native_rest::GeneratorNativeRest;
use holonic_engine::receiver_exact_compression::{InputId, ItemId, Observation, ReceiverId};
use holonic_engine::receiver_history_compression::NativeStateId;
use serde::{Deserialize, Serialize};

const REST: &str =
    "output/the_active_cover_condenses_into_a_generator_native_codec/generator-native-rest.json";
const EVIDENCE: &str =
    "output/the_active_cover_condenses_into_a_generator_native_codec/reconstruction-evidence.json";

#[derive(Clone, Debug, Deserialize)]
struct QuotientAssignment {
    source: ItemId,
    native: NativeStateId,
}

#[derive(Clone, Debug, Deserialize)]
struct ReconstructionFibre {
    native: NativeStateId,
    sources: Vec<ItemId>,
}

#[derive(Clone, Debug, Deserialize)]
struct FirstSeparator {
    left: ItemId,
    right: ItemId,
    distinguishing_word: Vec<InputId>,
    witness: [u64; 3],
    separated_by_terminus: bool,
}

#[derive(Deserialize)]
struct CompressionEvidence {
    quotient: Vec<QuotientAssignment>,
    reconstruction_fibres: Vec<ReconstructionFibre>,
    first_separators: Vec<FirstSeparator>,
}

#[derive(Deserialize)]
struct Evidence {
    receiver_history_compression: CompressionEvidence,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LeaderSelection {
    pub selection_law: String,
    pub source_left: ItemId,
    pub source_right: ItemId,
    pub port: NativeStateId,
    pub opposing_port: NativeStateId,
    pub leader_word: Vec<InputId>,
    pub return_word: Vec<InputId>,
    pub leader_endpoint: NativeStateId,
    pub opposing_endpoint: NativeStateId,
    pub receiver: ReceiverId,
    pub endpoint_observation: Observation,
    pub opposing_observation: Observation,
    pub separated_by_terminus: bool,
    pub complete_anchor_fibre: Vec<ItemId>,
}

pub struct NativeTrainingMount {
    pub rest_path: PathBuf,
    pub evidence_path: PathBuf,
    pub rest_bytes: Vec<u8>,
    pub leader: LeaderSelection,
}

pub fn mount(root: &Path) -> Result<NativeTrainingMount, String> {
    let rest_path = root.join(REST);
    let evidence_path = root.join(EVIDENCE);
    let rest_bytes = std::fs::read(&rest_path).map_err(|error| error.to_string())?;
    let rest = GeneratorNativeRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let evidence_bytes = std::fs::read(&evidence_path).map_err(|error| error.to_string())?;
    let evidence: Evidence =
        serde_json::from_slice(&evidence_bytes).map_err(|error| error.to_string())?;
    let compression = evidence.receiver_history_compression;
    let deepest = compression
        .first_separators
        .iter()
        .map(|separator| separator.distinguishing_word.len())
        .max()
        .ok_or_else(|| "M3 returned no successor separator".to_owned())?;
    let separator = compression
        .first_separators
        .iter()
        .filter(|separator| separator.distinguishing_word.len() == deepest)
        .min_by_key(|separator| (separator.left, separator.right))
        .ok_or_else(|| "M3 returned no deepest successor separator".to_owned())?;
    if separator.distinguishing_word.is_empty() {
        return Err("the selected leader has no interior".to_owned());
    }
    let quotient = compression
        .quotient
        .iter()
        .map(|assignment| (assignment.source, assignment.native))
        .collect::<BTreeMap<_, _>>();
    let port = *quotient
        .get(&separator.left)
        .ok_or_else(|| "the leader's left source has no quotient image".to_owned())?;
    let opposing_port = *quotient
        .get(&separator.right)
        .ok_or_else(|| "the leader's right source has no quotient image".to_owned())?;
    let leader_endpoint = rest
        .conduct_word(port, &separator.distinguishing_word)
        .map_err(|error| error.to_string())?;
    let opposing_endpoint = rest
        .conduct_word(opposing_port, &separator.distinguishing_word)
        .map_err(|error| error.to_string())?;
    let receiver = ReceiverId(separator.witness[0]);
    let endpoint_observation = rest
        .decode(leader_endpoint, receiver)
        .map_err(|error| error.to_string())?;
    let opposing_observation = rest
        .decode(opposing_endpoint, receiver)
        .map_err(|error| error.to_string())?;
    if endpoint_observation != Observation(separator.witness[1])
        || opposing_observation != Observation(separator.witness[2])
        || endpoint_observation == opposing_observation
    {
        return Err(
            "the selected M3 word no longer returns its addressed receiver difference".into(),
        );
    }
    let complete_anchor_fibre = compression
        .reconstruction_fibres
        .iter()
        .find(|fibre| fibre.native == port)
        .map(|fibre| fibre.sources.clone())
        .ok_or_else(|| "the selected native port has no complete source fibre".to_owned())?;
    let mut return_word = separator.distinguishing_word.clone();
    return_word.reverse();
    let leader = LeaderSelection {
        selection_law:
            "maximum returned successor depth; least addressed source pair at that depth".to_owned(),
        source_left: separator.left,
        source_right: separator.right,
        port,
        opposing_port,
        leader_word: separator.distinguishing_word.clone(),
        return_word,
        leader_endpoint,
        opposing_endpoint,
        receiver,
        endpoint_observation,
        opposing_observation,
        separated_by_terminus: separator.separated_by_terminus,
        complete_anchor_fibre,
    };
    Ok(NativeTrainingMount {
        rest_path,
        evidence_path,
        rest_bytes,
        leader,
    })
}
