//! Receiver questions over the mounted exchange atlas.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::interchange::{
    all_orders, certify_front, EnactedFace, EnactsInOrder, Interchange,
};
use num_bigint::BigUint;
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::{Digest32, ExchangeWorldTube, VisibleMessageFace};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScalarJoinWitness {
    pub class: u32,
    pub content_sha256: Digest32,
    pub left_node: u64,
    pub right_node: u64,
    pub left_occurrence: Digest32,
    pub right_occurrence: Digest32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactJoinPopulation {
    pub schema: String,
    pub left_key_face: String,
    pub right_key_face: String,
    pub cross_container_only: bool,
    pub left_population: u64,
    pub right_population: u64,
    pub matched_left: u64,
    pub unmatched_left: u64,
    pub ambiguous_left: u64,
    /// Exact cardinality of the represented pair population. The pairs remain factorized by
    /// contact class; a quadratic sheet is never materialized.
    pub pair_population: u64,
    /// One situated pair per inhabited join class. Complete membership remains in the world's
    /// `CorrespondenceFibres::class_members` and can be reopened without rescanning source bytes.
    pub witnesses: Vec<ScalarJoinWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BranchPermutationReceipt {
    pub schema: String,
    pub members: [Digest32; 2],
    pub forward_chronology: Digest32,
    pub reverse_chronology: Digest32,
    pub chronology_changed: bool,
    pub interchange_proved: bool,
    pub certificate_ordered: bool,
    pub separating_coordinate: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LineageAblationReceipt {
    pub schema: String,
    pub provider_faces_removed: u64,
    pub material_kind_faces_removed: u64,
    pub content_law_before: Digest32,
    pub content_law_after: Digest32,
    pub lineage_before: Digest32,
    pub lineage_after: Digest32,
    pub content_law_preserved: bool,
    pub lineage_changed: bool,
}

impl ExchangeWorldTube {
    /// Attach an exterior visible-language projection to records already in the richer atlas.
    pub fn attach_visible_messages(
        &mut self,
        mut faces: Vec<VisibleMessageFace>,
        visible_controls_excluded: u64,
    ) -> Result<(), String> {
        for face in &faces {
            let Some(record) = self.records.get(face.record as usize) else {
                return Err(format!(
                    "visible face {} names unknown record {}",
                    face.occurrence, face.record
                ));
            };
            if record.container != face.container || record.raw_range != face.raw_range {
                return Err(format!(
                    "visible face {} does not factor through its declared record occurrence",
                    face.occurrence
                ));
            }
        }
        faces.sort_by_key(|face| (face.container, face.raw_range.start, face.raw_range.end));
        self.visible_messages = faces;
        self.excluded.visible_membrane_controls = visible_controls_excluded;
        Ok(())
    }

    /// Open exact equal-scalar classes through two exterior object-key faces. The names ask a
    /// receiver question; the contact classes were already founded without them on the card.
    pub fn joins_between_key_faces(
        &self,
        left_key: &str,
        right_key: &str,
        cross_container_only: bool,
    ) -> ExactJoinPopulation {
        let class_of = self
            .scalar_sites
            .iter()
            .map(|site| (site.node, (site.class, site.content)))
            .collect::<BTreeMap<_, _>>();
        let mut left = Vec::new();
        let mut right = Vec::new();
        for field in &self.fields {
            let node =
                self.records[field.record as usize].node_from + u64::from(field.local.value_node);
            if field.local.key == left_key && class_of.contains_key(&node) {
                left.push(node);
            }
            if field.local.key == right_key && class_of.contains_key(&node) {
                right.push(node);
            }
        }
        let right_by_class =
            right
                .iter()
                .fold(BTreeMap::<u32, Vec<u64>>::new(), |mut map, node| {
                    map.entry(class_of[node].0).or_default().push(*node);
                    map
                });
        let mut representatives = BTreeMap::<u32, ScalarJoinWitness>::new();
        let mut matched_left = 0u64;
        let mut unmatched_left = 0u64;
        let mut ambiguous_left = 0u64;
        let mut pair_population = 0u64;
        for left_node in &left {
            let (class, content) = class_of[left_node];
            let left_record = self.nodes[*left_node as usize].record;
            let left_container = self.records[left_record as usize].container;
            let candidates = right_by_class
                .get(&class)
                .into_iter()
                .flatten()
                .filter(|right_node| {
                    if left_key == right_key && **right_node <= *left_node {
                        return false;
                    }
                    let right_record = self.nodes[**right_node as usize].record;
                    if right_record == left_record {
                        return false;
                    }
                    !cross_container_only
                        || self.records[right_record as usize].container != left_container
                })
                .copied()
                .collect::<Vec<_>>();
            match candidates.len() {
                0 => unmatched_left = unmatched_left.saturating_add(1),
                1 => matched_left = matched_left.saturating_add(1),
                _ => {
                    matched_left = matched_left.saturating_add(1);
                    ambiguous_left = ambiguous_left.saturating_add(1);
                }
            }
            pair_population = pair_population.saturating_add(candidates.len() as u64);
            if let Some(right_node) = candidates.first().copied() {
                representatives
                    .entry(class)
                    .or_insert_with(|| ScalarJoinWitness {
                        class,
                        content_sha256: content,
                        left_node: *left_node,
                        right_node,
                        left_occurrence: self.node_occurrence(*left_node),
                        right_occurrence: self.node_occurrence(right_node),
                    });
            }
        }
        ExactJoinPopulation {
            schema: "soma-life.exchange-exact-join-population.v1".to_owned(),
            left_key_face: left_key.to_owned(),
            right_key_face: right_key.to_owned(),
            cross_container_only,
            left_population: left.len() as u64,
            right_population: right.len() as u64,
            matched_left,
            unmatched_left,
            ambiguous_left,
            pair_population,
            witnesses: representatives.into_values().collect(),
        }
    }

    pub fn lineage_ablation(
        &self,
        remove_provider: bool,
        remove_material_kind: bool,
    ) -> LineageAblationReceipt {
        let before = lineage_digest(self, false, false);
        let after = lineage_digest(self, remove_provider, remove_material_kind);
        let provider_faces_removed = if remove_provider {
            self.containers.len() as u64
        } else {
            0
        };
        let material_kind_faces_removed = if remove_material_kind {
            self.containers.len() as u64
        } else {
            0
        };
        LineageAblationReceipt {
            schema: "soma-life.exchange-lineage-ablation.v1".to_owned(),
            provider_faces_removed,
            material_kind_faces_removed,
            content_law_before: self.content_law_sha256,
            content_law_after: content_law_digest(self),
            lineage_before: before,
            lineage_after: after,
            content_law_preserved: self.content_law_sha256 == content_law_digest(self),
            lineage_changed: before != after,
        }
    }

    pub fn repeated_visible_content_population(&self) -> BTreeMap<Digest32, Vec<Digest32>> {
        let mut by_content = BTreeMap::<Digest32, Vec<Digest32>>::new();
        for face in &self.visible_messages {
            by_content
                .entry(face.text_sha256)
                .or_default()
                .push(self.record_occurrence(face.record));
        }
        by_content.retain(|_, occurrences| {
            occurrences.sort();
            occurrences.dedup();
            occurrences.len() > 1
        });
        by_content
    }

    /// Ask the existing complete-return interchange owner whether two situated records may swap.
    pub fn branch_permutation_receipt(
        &self,
        left_record: u64,
        right_record: u64,
    ) -> BranchPermutationReceipt {
        let members = [
            self.record_occurrence(left_record),
            self.record_occurrence(right_record),
        ];
        let mut enactor = ChronologyEnactor {
            members,
            returns: Vec::new(),
        };
        let certificate = certify_front(&all_orders(2), &mut enactor);
        let forward = chronology_digest(&members);
        let reverse = chronology_digest(&[members[1], members[0]]);
        BranchPermutationReceipt {
            schema: "soma-life.exchange-branch-permutation.v1".to_owned(),
            members,
            forward_chronology: forward,
            reverse_chronology: reverse,
            chronology_changed: forward != reverse,
            interchange_proved: certificate.is_interchangeable(),
            certificate_ordered: matches!(certificate.verdict, Interchange::Ordered { .. }),
            separating_coordinate: "chronology/ordered-record-occurrence-word".to_owned(),
        }
    }
}

pub(crate) fn content_law_digest(world: &ExchangeWorldTube) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update(b"exchange-content-law/v1");
    digest.update(world.source_occurrence_sha256.octets());
    digest.update((world.records.len() as u64).to_le_bytes());
    for record in &world.records {
        digest.update(record.container.to_le_bytes());
        digest.update(record.ordinal.to_le_bytes());
        digest.update(record.raw_range.start.to_le_bytes());
        digest.update(record.raw_range.end.to_le_bytes());
        digest.update(record.raw_sha256.octets());
        digest.update(record.root_sha256.octets());
    }
    digest.update((world.nodes.len() as u64).to_le_bytes());
    for node in &world.nodes {
        digest.update(node.record.to_le_bytes());
        digest.update(node.local.parent.unwrap_or(u32::MAX).to_le_bytes());
        digest.update(node.local.position.to_le_bytes());
        digest.update([node.local.kind.wire()]);
        digest.update(node.local.content.octets());
    }
    digest.update((world.scalar_sites.len() as u64).to_le_bytes());
    for site in &world.scalar_sites {
        digest.update(site.node.to_le_bytes());
        digest.update(site.content.octets());
        digest.update(site.class.to_le_bytes());
    }
    Digest32::from_sha(digest.finalize())
}

fn lineage_digest(
    world: &ExchangeWorldTube,
    without_provider: bool,
    without_kind: bool,
) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update(b"exchange-exterior-lineage/v1");
    for container in &world.containers {
        digest.update(container.ordinal.to_le_bytes());
        digest.update(container.lineage.locator.as_os_str().as_encoded_bytes());
        if !without_provider {
            digest.update(container.lineage.provider.as_bytes());
        }
        if !without_kind {
            digest.update(container.lineage.material_kind.as_bytes());
        }
    }
    Digest32::from_sha(digest.finalize())
}

fn chronology_digest(order: &[Digest32]) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update(b"exchange-chronology-receiver/v1");
    digest.update((order.len() as u64).to_le_bytes());
    for occurrence in order {
        digest.update(occurrence.octets());
    }
    Digest32::from_sha(digest.finalize())
}

struct ChronologyEnactor {
    members: [Digest32; 2],
    returns: Vec<Digest32>,
}

impl EnactsInOrder for ChronologyEnactor {
    fn enact_in(&mut self, order: &[usize]) -> Result<EnactedFace, String> {
        if order.len() != 2 || order.iter().any(|member| *member >= 2) {
            return Err("the branch receiver accepts exactly the declared two members".to_owned());
        }
        let word = [self.members[order[0]], self.members[order[1]]];
        let returned = chronology_digest(&word);
        self.returns.push(returned);
        let mut face = EnactedFace::default();
        face.conduct
            .insert("chronology".to_owned(), returned.render());
        face.lineage.insert(
            "chronology".to_owned(),
            BTreeSet::from([word[0].render(), word[1].render()]),
        );
        face.resources
            .insert("records".to_owned(), BigUint::from(2u32));
        face.capacities
            .insert("occurrence-word".to_owned(), BigUint::from(2u32));
        Ok(face)
    }

    fn endpoints_disagree(&mut self, a: usize, b: usize) -> Result<Vec<(String, u64)>, String> {
        let left = self
            .returns
            .get(a)
            .ok_or_else(|| "missing first chronology return".to_owned())?;
        let right = self
            .returns
            .get(b)
            .ok_or_else(|| "missing second chronology return".to_owned())?;
        Ok(if left == right {
            Vec::new()
        } else {
            vec![("chronology/ordered-record-occurrence-word".to_owned(), 1)]
        })
    }
}
