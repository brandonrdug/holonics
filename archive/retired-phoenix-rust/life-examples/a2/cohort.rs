//! Provider-neutral sibling histories derived from A1's repeated visible-content fibres.

use std::collections::BTreeMap;

use life::exchange_world_tube::{Digest32, ExchangeWorldTube, VisibleMessageFace};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistoryMessage {
    pub occurrence: String,
    pub container: u32,
    pub record: u64,
    pub content_sha256: Digest32,
    pub text: String,
    pub provider_face: String,
    pub speaker_face: String,
    pub phase_face: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistorySeparator {
    pub against_prompt_occurrence: String,
    pub suffix_messages: Option<usize>,
    pub separating_face: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindowJoinWitness {
    pub class: u32,
    pub left_node: u64,
    pub right_node: u64,
    pub left_occurrence: Digest32,
    pub right_occurrence: Digest32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindowJoinPopulation {
    pub left_key_face: String,
    pub right_key_face: String,
    pub left_population: u64,
    pub right_population: u64,
    pub pair_population: u64,
    pub representatives: Vec<WindowJoinWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExteriorWorldConsequence {
    pub record_window: (u64, u64),
    pub parent_returns: WindowJoinPopulation,
    pub claude_tool_returns: WindowJoinPopulation,
    pub codex_tool_returns: WindowJoinPopulation,
    pub later_operator_return: Option<HistoryMessage>,
    pub open_fibres: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiblingHistoryCut {
    pub occurrence: String,
    pub repeated_content_sha256: Digest32,
    pub repeated_class_population: usize,
    pub prompt: HistoryMessage,
    pub history: Vec<HistoryMessage>,
    pub sibling: HistoryMessage,
    pub shortest_separators: Vec<HistorySeparator>,
    pub content_history_is_unique: bool,
    pub world: ExteriorWorldConsequence,
    pub native_history_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CohortExclusion {
    pub repeated_content_sha256: Digest32,
    pub prompt_occurrence: String,
    pub obstruction: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiblingCohort {
    pub schema: String,
    pub source_occurrence_sha256: Digest32,
    pub repeated_content_classes: usize,
    pub repeated_content_occurrences: usize,
    pub cuts: Vec<SiblingHistoryCut>,
    pub exclusions: Vec<CohortExclusion>,
    pub selection_law: String,
    pub provider_or_speaker_routes_selection: bool,
    pub truth_status: String,
}

pub fn derive(world: &ExchangeWorldTube) -> Result<SiblingCohort, String> {
    let mut sequences = BTreeMap::<u32, Vec<&VisibleMessageFace>>::new();
    for face in &world.visible_messages {
        sequences.entry(face.container).or_default().push(face);
    }
    for sequence in sequences.values_mut() {
        sequence.sort_by_key(|face| (face.raw_range.start, face.raw_range.end, face.record));
    }

    let mut repeated = BTreeMap::<Digest32, Vec<(u32, usize)>>::new();
    for (container, sequence) in &sequences {
        for (at, face) in sequence.iter().enumerate() {
            repeated
                .entry(face.text_sha256)
                .or_default()
                .push((*container, at));
        }
    }
    repeated.retain(|_, members| members.len() > 1);

    let scalar_class = world
        .scalar_sites
        .iter()
        .map(|site| (site.node, site.class))
        .collect::<BTreeMap<_, _>>();
    let repeated_content_occurrences = repeated.values().map(Vec::len).sum();
    let mut cuts = Vec::new();
    let mut exclusions = Vec::new();

    for (content, members) in &repeated {
        for (container, at) in members {
            let sequence = &sequences[container];
            let prompt = sequence[*at];
            let Some(sibling) = sequence.get(*at + 1).copied() else {
                exclusions.push(CohortExclusion {
                    repeated_content_sha256: *content,
                    prompt_occurrence: prompt.occurrence.clone(),
                    obstruction: "the repeated occurrence has no later visible occurrence inside its captured container prefix".to_owned(),
                });
                continue;
            };

            let mut separators = Vec::new();
            let mut required_suffix = 1usize;
            let mut unique = true;
            for (other_container, other_at) in members {
                if container == other_container && at == other_at {
                    continue;
                }
                let other_sequence = &sequences[other_container];
                let depth = shortest_content_suffix(sequence, *at, other_sequence, *other_at);
                unique &= depth.is_some();
                if let Some(depth) = depth {
                    required_suffix = required_suffix.max(depth);
                }
                separators.push(HistorySeparator {
                    against_prompt_occurrence: other_sequence[*other_at].occurrence.clone(),
                    suffix_messages: depth,
                    separating_face: if depth.is_some() {
                        "ordered visible-content suffix including its source boundary".to_owned()
                    } else {
                        "open: the complete available content histories agree".to_owned()
                    },
                });
            }
            if !unique {
                required_suffix = *at + 1;
            }
            let from = (*at + 1).saturating_sub(required_suffix);
            let history = sequence[from..=*at]
                .iter()
                .map(|face| message(face))
                .collect::<Vec<_>>();
            let later_operator = sequence
                .iter()
                .skip(*at + 2)
                .find(|face| face.speaker_face == prompt.speaker_face)
                .map(|face| message(face));
            let sibling_record = &world.records[sibling.record as usize];
            let until_ordinal = later_operator
                .as_ref()
                .map(|face| world.records[face.record as usize].ordinal)
                .unwrap_or_else(|| world.containers[*container as usize].record_extent);
            let window = sibling_record.ordinal..until_ordinal;
            let world_return = ExteriorWorldConsequence {
                record_window: (window.start, window.end),
                parent_returns: window_join(
                    world,
                    &scalar_class,
                    *container,
                    window.clone(),
                    "parentUuid",
                    "uuid",
                ),
                claude_tool_returns: window_join(
                    world,
                    &scalar_class,
                    *container,
                    window.clone(),
                    "tool_use_id",
                    "id",
                ),
                codex_tool_returns: window_join(
                    world,
                    &scalar_class,
                    *container,
                    window,
                    "call_id",
                    "call_id",
                ),
                later_operator_return: later_operator,
                open_fibres: Vec::new(),
            };
            let native_history_sha256 = history_digest(&history);
            let occurrence = addressed(&[
                b"athena-a2-history-cut/v1",
                &world.source_occurrence_sha256.octets(),
                prompt.occurrence.as_bytes(),
                sibling.occurrence.as_bytes(),
                native_history_sha256.as_bytes(),
            ]);
            cuts.push(SiblingHistoryCut {
                occurrence,
                repeated_content_sha256: *content,
                repeated_class_population: members.len(),
                prompt: message(prompt),
                history,
                sibling: message(sibling),
                shortest_separators: separators,
                content_history_is_unique: unique,
                world: world_return,
                native_history_sha256,
            });
        }
    }
    cuts.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    exclusions.sort_by(|left, right| {
        (&left.prompt_occurrence, left.repeated_content_sha256)
            .cmp(&(&right.prompt_occurrence, right.repeated_content_sha256))
    });

    Ok(SiblingCohort {
        schema: "soma-life.athena-a2-sibling-cohort.v1".to_owned(),
        source_occurrence_sha256: world.source_occurrence_sha256,
        repeated_content_classes: repeated.len(),
        repeated_content_occurrences,
        cuts,
        exclusions,
        selection_law: "all repeated visible-content classes; every member with one later visible occurrence; the shortest ordered content-history suffix separating that member from every twin, or its complete unresolved prefix".to_owned(),
        provider_or_speaker_routes_selection: false,
        truth_status: "established-bounded".to_owned(),
    })
}

fn shortest_content_suffix(
    left: &[&VisibleMessageFace],
    left_at: usize,
    right: &[&VisibleMessageFace],
    right_at: usize,
) -> Option<usize> {
    let maximum = (left_at + 1).max(right_at + 1);
    for depth in 1..=maximum {
        if depth > left_at + 1 || depth > right_at + 1 {
            return Some(depth);
        }
        let left_suffix = &left[left_at + 1 - depth..=left_at];
        let right_suffix = &right[right_at + 1 - depth..=right_at];
        if left_suffix
            .iter()
            .map(|face| face.text_sha256)
            .ne(right_suffix.iter().map(|face| face.text_sha256))
        {
            return Some(depth);
        }
    }
    None
}

fn window_join(
    world: &ExchangeWorldTube,
    scalar_class: &BTreeMap<u64, u32>,
    container: u32,
    ordinal_window: std::ops::Range<u64>,
    left_key: &str,
    right_key: &str,
) -> WindowJoinPopulation {
    let mut left = Vec::new();
    let mut right = Vec::new();
    for field in &world.fields {
        let record = &world.records[field.record as usize];
        if record.container != container
            || record.ordinal < ordinal_window.start
            || record.ordinal >= ordinal_window.end
        {
            continue;
        }
        let node = record.node_from + u64::from(field.local.value_node);
        if !scalar_class.contains_key(&node) {
            continue;
        }
        if field.local.key == left_key {
            left.push(node);
        }
        if field.local.key == right_key {
            right.push(node);
        }
    }
    let mut pair_population = 0u64;
    let mut representatives = BTreeMap::<u32, WindowJoinWitness>::new();
    for left_node in &left {
        let class = scalar_class[left_node];
        let left_record = world.nodes[*left_node as usize].record;
        for right_node in &right {
            if scalar_class[right_node] != class {
                continue;
            }
            if left_key == right_key && right_node <= left_node {
                continue;
            }
            let right_record = world.nodes[*right_node as usize].record;
            if left_record == right_record {
                continue;
            }
            pair_population = pair_population.saturating_add(1);
            representatives
                .entry(class)
                .or_insert_with(|| WindowJoinWitness {
                    class,
                    left_node: *left_node,
                    right_node: *right_node,
                    left_occurrence: world.node_occurrence(*left_node),
                    right_occurrence: world.node_occurrence(*right_node),
                });
        }
    }
    WindowJoinPopulation {
        left_key_face: left_key.to_owned(),
        right_key_face: right_key.to_owned(),
        left_population: left.len() as u64,
        right_population: right.len() as u64,
        pair_population,
        representatives: representatives.into_values().collect(),
    }
}

fn message(face: &VisibleMessageFace) -> HistoryMessage {
    HistoryMessage {
        occurrence: face.occurrence.clone(),
        container: face.container,
        record: face.record,
        content_sha256: face.text_sha256,
        text: face.text.clone(),
        provider_face: face.provider_face.clone(),
        speaker_face: face.speaker_face.clone(),
        phase_face: face.phase_face.clone(),
    }
}

fn history_digest(history: &[HistoryMessage]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"athena-a2-native-history/v1");
    digest.update((history.len() as u64).to_le_bytes());
    for message in history {
        framed(&mut digest, message.occurrence.as_bytes());
        digest.update(message.content_sha256.octets());
    }
    hex(&digest.finalize())
}

fn addressed(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        framed(&mut digest, part);
    }
    hex(&digest.finalize())
}

fn framed(digest: &mut Sha256, bytes: &[u8]) {
    digest.update((bytes.len() as u64).to_le_bytes());
    digest.update(bytes);
}

pub fn provider_neutral_digest(cohort: &SiblingCohort) -> String {
    let mut digest = Sha256::new();
    digest.update(b"athena-a2-provider-neutral-cohort/v1");
    for cut in &cohort.cuts {
        framed(&mut digest, cut.occurrence.as_bytes());
        framed(&mut digest, cut.native_history_sha256.as_bytes());
        framed(&mut digest, cut.sibling.occurrence.as_bytes());
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
