//! Addressed complete user-to-assistant continuation families over one exchange world-tube.
//!
//! The atlas stores indices and exact content addresses rather than copying message text into each
//! history. Complete response surfaces remain in the one world owner until the exterior source is
//! withdrawn. The final cultivated rest therefore cannot accidentally become a transcript.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{Digest32, ExchangeWorldTube, VisibleMessageFace};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MessageAddress {
    pub visible_index: u64,
    pub occurrence: String,
    pub content_sha256: Digest32,
    pub container: u32,
    pub record: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ContinuationPartition {
    Development,
    HeldOut,
    Revisit,
    Rebase,
    DisjointControl,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShortestHistorySeparator {
    pub against_family: String,
    pub visible_suffix_depth: Option<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContinuationWorldWindow {
    pub record_ordinal_from: u64,
    pub record_ordinal_until: u64,
    pub parent_join_pairs: u64,
    pub claude_tool_join_pairs: u64,
    pub codex_tool_join_pairs: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContinuationFamily {
    pub occurrence: String,
    pub partition: ContinuationPartition,
    pub prompt: MessageAddress,
    pub history: Vec<MessageAddress>,
    pub response: Vec<MessageAddress>,
    pub later_operator_return: Option<MessageAddress>,
    pub prompt_kinship_population: usize,
    pub response_kinship_population: usize,
    pub response_sha256: Digest32,
    pub shortest_separators: Vec<ShortestHistorySeparator>,
    pub world: ContinuationWorldWindow,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContinuationExclusion {
    pub container: u32,
    pub visible_index: Option<u64>,
    pub occurrence: Option<String>,
    pub obstruction: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContinuationAperture {
    pub schema: String,
    pub source_occurrence_sha256: Digest32,
    pub families: Vec<ContinuationFamily>,
    pub exclusions: Vec<ContinuationExclusion>,
    pub partition_population: BTreeMap<ContinuationPartition, usize>,
    pub complete_response_message_population: usize,
    pub response_text_copied_into_atlas: bool,
    pub provider_or_material_kind_routes_partition: bool,
}

pub fn derive_continuation_aperture(
    world: &ExchangeWorldTube,
) -> Result<ContinuationAperture, String> {
    let mut sequences = BTreeMap::<u32, Vec<usize>>::new();
    for (index, face) in world.visible_messages.iter().enumerate() {
        sequences.entry(face.container).or_default().push(index);
    }
    for sequence in sequences.values_mut() {
        sequence.sort_by_key(|index| {
            let face = &world.visible_messages[*index];
            (face.raw_range.start, face.raw_range.end, face.record)
        });
    }

    struct Staged {
        prompt: usize,
        history: Vec<usize>,
        response: Vec<usize>,
        later: Option<usize>,
        response_sha256: Digest32,
        world: ContinuationWorldWindow,
    }
    let scalar_class = world
        .scalar_sites
        .iter()
        .map(|site| (site.node, site.class))
        .collect::<BTreeMap<_, _>>();
    let mut staged = Vec::<Staged>::new();
    let mut exclusions = Vec::new();
    for (container, sequence) in &sequences {
        let mut at = 0usize;
        while at < sequence.len() {
            let face = &world.visible_messages[sequence[at]];
            if face.speaker_face != "user" {
                at += 1;
                continue;
            }
            let prompt_at = at;
            let mut response_from = at + 1;
            while response_from < sequence.len()
                && world.visible_messages[sequence[response_from]].speaker_face != "assistant"
                && world.visible_messages[sequence[response_from]].speaker_face != "user"
            {
                response_from += 1;
            }
            if response_from >= sequence.len()
                || world.visible_messages[sequence[response_from]].speaker_face == "user"
            {
                exclusions.push(ContinuationExclusion {
                    container: *container,
                    visible_index: Some(sequence[prompt_at] as u64),
                    occurrence: Some(face.occurrence.clone()),
                    obstruction: "the user occurrence has no later visible assistant continuation inside its captured prefix".to_owned(),
                });
                at += 1;
                continue;
            }
            let mut response_until = response_from;
            while response_until < sequence.len()
                && world.visible_messages[sequence[response_until]].speaker_face == "assistant"
            {
                response_until += 1;
            }
            let response = sequence[response_from..response_until].to_vec();
            let later = sequence[response_until..]
                .iter()
                .copied()
                .find(|index| world.visible_messages[*index].speaker_face == "user");
            let history_from = (0..prompt_at)
                .rev()
                .find(|prior| world.visible_messages[sequence[*prior]].speaker_face == "user")
                .unwrap_or(prompt_at);
            let history = sequence[history_from..=prompt_at].to_vec();
            let response_sha256 =
                response_digest(response.iter().map(|index| &world.visible_messages[*index]));
            let first_record = &world.records[world.visible_messages[response[0]].record as usize];
            let until = later
                .map(|index| world.records[world.visible_messages[index].record as usize].ordinal)
                .unwrap_or(world.containers[*container as usize].record_extent);
            let window = first_record.ordinal..until;
            staged.push(Staged {
                prompt: sequence[prompt_at],
                history,
                response,
                later,
                response_sha256,
                world: ContinuationWorldWindow {
                    record_ordinal_from: window.start,
                    record_ordinal_until: window.end,
                    parent_join_pairs: window_join_count(
                        world,
                        &scalar_class,
                        *container,
                        window.clone(),
                        "parentUuid",
                        "uuid",
                    ),
                    claude_tool_join_pairs: window_join_count(
                        world,
                        &scalar_class,
                        *container,
                        window.clone(),
                        "tool_use_id",
                        "id",
                    ),
                    codex_tool_join_pairs: window_join_count(
                        world,
                        &scalar_class,
                        *container,
                        window,
                        "call_id",
                        "call_id",
                    ),
                },
            });
            at = response_until;
        }
    }

    let mut prompt_classes = BTreeMap::<Digest32, Vec<usize>>::new();
    let mut response_classes = BTreeMap::<Digest32, Vec<usize>>::new();
    for (index, family) in staged.iter().enumerate() {
        prompt_classes
            .entry(world.visible_messages[family.prompt].text_sha256)
            .or_default()
            .push(index);
        response_classes
            .entry(family.response_sha256)
            .or_default()
            .push(index);
    }
    let mut partitions = vec![ContinuationPartition::DisjointControl; staged.len()];
    for members in prompt_classes.values_mut() {
        members.sort_by_key(|index| {
            let prompt = &world.visible_messages[staged[*index].prompt];
            (prompt.container, prompt.raw_range.start, prompt.record)
        });
        match members.as_slice() {
            [] => {}
            [only] => {
                if response_classes[&staged[*only].response_sha256].len() > 1 {
                    partitions[*only] = ContinuationPartition::Rebase;
                }
            }
            [development, held_out] => {
                partitions[*development] = ContinuationPartition::Development;
                partitions[*held_out] = ContinuationPartition::HeldOut;
            }
            [development, held_out, remainder @ ..] => {
                partitions[*development] = ContinuationPartition::Development;
                partitions[*held_out] = ContinuationPartition::HeldOut;
                for revisit in remainder {
                    partitions[*revisit] = ContinuationPartition::Revisit;
                }
            }
        }
    }

    let family_occurrences = staged
        .iter()
        .map(|family| {
            addressed(&[
                b"athena-alpha/continuation-family/v1",
                &world.source_occurrence_sha256.octets(),
                world.visible_messages[family.prompt].occurrence.as_bytes(),
                &family.response_sha256.octets(),
            ])
        })
        .collect::<Vec<_>>();
    let mut families = Vec::with_capacity(staged.len());
    for (index, family) in staged.iter().enumerate() {
        let prompt = &world.visible_messages[family.prompt];
        let prompt_members = &prompt_classes[&prompt.text_sha256];
        let separators = prompt_members
            .iter()
            .copied()
            .filter(|other| *other != index)
            .map(|other| ShortestHistorySeparator {
                against_family: family_occurrences[other].clone(),
                visible_suffix_depth: shortest_history_separator(
                    &family.history,
                    &staged[other].history,
                    &world.visible_messages,
                ),
            })
            .collect();
        families.push(ContinuationFamily {
            occurrence: family_occurrences[index].clone(),
            partition: partitions[index],
            prompt: address(family.prompt, &world.visible_messages[family.prompt]),
            history: family
                .history
                .iter()
                .map(|at| address(*at, &world.visible_messages[*at]))
                .collect(),
            response: family
                .response
                .iter()
                .map(|at| address(*at, &world.visible_messages[*at]))
                .collect(),
            later_operator_return: family
                .later
                .map(|at| address(at, &world.visible_messages[at])),
            prompt_kinship_population: prompt_members.len(),
            response_kinship_population: response_classes[&family.response_sha256].len(),
            response_sha256: family.response_sha256,
            shortest_separators: separators,
            world: family.world.clone(),
        });
    }
    families.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    exclusions.sort_by(|left, right| {
        (left.container, left.visible_index, &left.occurrence).cmp(&(
            right.container,
            right.visible_index,
            &right.occurrence,
        ))
    });
    let mut partition_population = BTreeMap::new();
    for family in &families {
        *partition_population.entry(family.partition).or_insert(0) += 1;
    }
    Ok(ContinuationAperture {
        schema: "soma-life.athena-alpha-continuation-aperture.v1".to_owned(),
        source_occurrence_sha256: world.source_occurrence_sha256,
        complete_response_message_population: families
            .iter()
            .map(|family| family.response.len())
            .sum(),
        families,
        exclusions,
        partition_population,
        response_text_copied_into_atlas: false,
        provider_or_material_kind_routes_partition: false,
    })
}

fn address(index: usize, face: &VisibleMessageFace) -> MessageAddress {
    MessageAddress {
        visible_index: index as u64,
        occurrence: face.occurrence.clone(),
        content_sha256: face.text_sha256,
        container: face.container,
        record: face.record,
    }
}

fn response_digest<'a>(faces: impl IntoIterator<Item = &'a VisibleMessageFace>) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update(b"athena-alpha/complete-response/v1");
    for face in faces {
        digest.update(face.text_sha256.octets());
    }
    Digest32::from_sha(digest.finalize())
}

fn shortest_history_separator(
    left: &[usize],
    right: &[usize],
    visible: &[VisibleMessageFace],
) -> Option<usize> {
    let maximum = left.len().max(right.len());
    for depth in 1..=maximum {
        if depth > left.len() || depth > right.len() {
            return Some(depth);
        }
        if left[left.len() - depth..]
            .iter()
            .map(|index| visible[*index].text_sha256)
            .ne(right[right.len() - depth..]
                .iter()
                .map(|index| visible[*index].text_sha256))
        {
            return Some(depth);
        }
    }
    None
}

fn window_join_count(
    world: &ExchangeWorldTube,
    scalar_class: &BTreeMap<u64, u32>,
    container: u32,
    window: std::ops::Range<u64>,
    left_key: &str,
    right_key: &str,
) -> u64 {
    let mut left = Vec::new();
    let mut right = Vec::new();
    for field in &world.fields {
        let record = &world.records[field.record as usize];
        if record.container != container
            || record.ordinal < window.start
            || record.ordinal >= window.end
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
    let mut pairs = 0u64;
    for left_node in &left {
        for right_node in &right {
            if scalar_class[left_node] != scalar_class[right_node]
                || (left_key == right_key && right_node <= left_node)
                || world.nodes[*left_node as usize].record
                    == world.nodes[*right_node as usize].record
            {
                continue;
            }
            pairs = pairs.saturating_add(1);
        }
    }
    pairs
}

fn addressed(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    Digest32::from_sha(digest.finalize()).render()
}
