use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use sha2::{Digest, Sha256};

use crate::exchange_world_tube::{ContinuationAperture, ContinuationFamily, MessageAddress};

use super::types::{
    CausalSectionAddress, ReceiverGrain, TransportGeneratorAddress, TransportSpecies,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ExactFace {
    Surface([u8; 32]),
    Boundary(u64, bool),
    World(u64, u64, u64, u64),
    Port(u64, u64, u64),
}

pub(super) struct LaboratorySections {
    pub items: Vec<ItemId>,
    pub rich_receivers: Vec<ReceiverId>,
    pub inputs: Vec<InputId>,
    pub observations: BTreeMap<(ItemId, ReceiverId), Observation>,
    pub successors: BTreeMap<(ItemId, InputId), ItemId>,
    pub sections: Vec<CausalSectionAddress>,
    pub generators: Vec<TransportGeneratorAddress>,
    pub family_by_item: BTreeMap<ItemId, String>,
    pub aperture_family_by_item: BTreeMap<ItemId, usize>,
    pub supports: BTreeMap<ItemId, BTreeSet<String>>,
}

pub(super) struct SystemView<'a> {
    pub sections: &'a LaboratorySections,
    pub receivers: &'a [ReceiverId],
}

impl ObservedSystem for SystemView<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.sections.items.clone()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.receivers.to_vec()
    }

    fn inputs(&self) -> Vec<InputId> {
        self.sections.inputs.clone()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.sections.observations[&(item, receiver)]
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.sections.successors.get(&(item, input)).copied()
    }
}

impl LaboratorySections {
    pub fn found(aperture: &ContinuationAperture) -> Result<Self, String> {
        if aperture.families.is_empty() {
            return Err("the continuation aperture contains no causal sections".to_owned());
        }
        let mut families = aperture.families.iter().enumerate().collect::<Vec<_>>();
        families.sort_by_key(|(_, family)| {
            (
                family.prompt.container,
                family.prompt.record,
                family.prompt.visible_index,
            )
        });
        let items = (0..families.len())
            .map(|at| ItemId(at as u64))
            .collect::<Vec<_>>();
        let family_by_item = families
            .iter()
            .zip(&items)
            .map(|((_, family), item)| (*item, section_occurrence(aperture, family)))
            .collect::<BTreeMap<_, _>>();
        let aperture_family_by_item = families
            .iter()
            .zip(&items)
            .map(|((at, _), item)| (*item, *at))
            .collect::<BTreeMap<_, _>>();
        let item_by_prompt = families
            .iter()
            .zip(&items)
            .map(|((_, family), item)| (message_key(&family.prompt), *item))
            .collect::<BTreeMap<_, _>>();

        let sections = families
            .iter()
            .zip(&items)
            .map(|((_, family), item)| CausalSectionAddress {
                source_item: item.0,
                family_occurrence: family_by_item[item].clone(),
                predecessor_family_address: family.occurrence.clone(),
                prompt_occurrence: situated_message(&family.prompt),
                history_occurrences: family.history.iter().map(situated_message).collect(),
                response_occurrences: family.response.iter().map(situated_message).collect(),
                later_return_occurrence: family
                    .later_operator_return
                    .as_ref()
                    .map(situated_message),
                returned_surface_sha256: family.response_sha256.render(),
            })
            .collect::<Vec<_>>();
        let supports = items
            .iter()
            .zip(&sections)
            .map(|(item, section)| {
                let mut support = section
                    .history_occurrences
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>();
                support.extend(section.response_occurrences.iter().cloned());
                support.insert(section.prompt_occurrence.clone());
                if let Some(later) = &section.later_return_occurrence {
                    support.insert(later.clone());
                }
                (*item, support)
            })
            .collect::<BTreeMap<_, _>>();

        let rich_receivers = [
            ReceiverGrain::ReturnedSurface,
            ReceiverGrain::BoundaryIncidence,
            ReceiverGrain::WorldConsequence,
            ReceiverGrain::ContinuationPort,
        ]
        .into_iter()
        .map(ReceiverGrain::id)
        .collect::<Vec<_>>();
        let ordered_families = families
            .iter()
            .map(|(_, family)| *family)
            .collect::<Vec<_>>();
        let observations = observations(&ordered_families, &items);

        let mut successors = BTreeMap::new();
        let mut generators = Vec::new();
        let exterior = InputId(0);
        let exterior_targets = ordered_families
            .iter()
            .zip(&items)
            .map(|(family, item)| {
                let target = family
                    .later_operator_return
                    .as_ref()
                    .and_then(|later| item_by_prompt.get(&message_key(later)))
                    .copied()
                    .unwrap_or(*item);
                (*item, target)
            })
            .collect::<BTreeMap<_, _>>();
        install_total(&items, exterior, &exterior_targets, &mut successors);
        generators.push(generator_address(
            exterior,
            TransportSpecies::ExteriorReturn,
            &exterior_targets,
            &family_by_item,
            None,
        ));

        let rebase = InputId(1);
        let rebase_targets = exact_rebase_targets(&ordered_families, &items);
        install_total(&items, rebase, &rebase_targets, &mut successors);
        generators.push(generator_address(
            rebase,
            TransportSpecies::ExactRebase,
            &rebase_targets,
            &family_by_item,
            Some(rebase),
        ));

        Ok(Self {
            items,
            rich_receivers,
            inputs: vec![exterior, rebase],
            observations,
            successors,
            sections,
            generators,
            family_by_item,
            aperture_family_by_item,
            supports,
        })
    }

    pub fn rich_view(&self) -> SystemView<'_> {
        SystemView {
            sections: self,
            receivers: &self.rich_receivers,
        }
    }

    pub fn surface_view(&self) -> SystemView<'_> {
        SystemView {
            sections: self,
            receivers: &self.rich_receivers[..1],
        }
    }

    pub fn successor(&self, item: ItemId, input: InputId) -> ItemId {
        self.successors[&(item, input)]
    }
}

fn observations(
    families: &[&ContinuationFamily],
    items: &[ItemId],
) -> BTreeMap<(ItemId, ReceiverId), Observation> {
    let mut faces = BTreeMap::<ReceiverId, BTreeMap<ExactFace, u64>>::new();
    let mut out = BTreeMap::new();
    for (family, item) in families.iter().zip(items) {
        let readings = [
            (
                ReceiverGrain::ReturnedSurface.id(),
                ExactFace::Surface(family.response_sha256.octets()),
            ),
            (
                ReceiverGrain::BoundaryIncidence.id(),
                ExactFace::Boundary(
                    family.response.len() as u64,
                    family.later_operator_return.is_some(),
                ),
            ),
            (
                ReceiverGrain::WorldConsequence.id(),
                ExactFace::World(
                    family
                        .world
                        .record_ordinal_until
                        .saturating_sub(family.world.record_ordinal_from),
                    family.world.parent_join_pairs,
                    family.world.claude_tool_join_pairs,
                    family.world.codex_tool_join_pairs,
                ),
            ),
            (
                ReceiverGrain::ContinuationPort.id(),
                ExactFace::Port(
                    family.history.len() as u64,
                    family.prompt_kinship_population as u64,
                    family.response_kinship_population as u64,
                ),
            ),
        ];
        for (receiver, face) in readings {
            let receiver_faces = faces.entry(receiver).or_default();
            let next = receiver_faces.len() as u64;
            let identity = *receiver_faces.entry(face).or_insert(next);
            out.insert((*item, receiver), Observation(identity));
        }
    }
    out
}

fn exact_rebase_targets(
    families: &[&ContinuationFamily],
    items: &[ItemId],
) -> BTreeMap<ItemId, ItemId> {
    let mut classes = BTreeMap::<[u8; 32], Vec<ItemId>>::new();
    for (family, item) in families.iter().zip(items) {
        classes
            .entry(family.response_sha256.octets())
            .or_default()
            .push(*item);
    }
    let mut targets = items
        .iter()
        .map(|item| (*item, *item))
        .collect::<BTreeMap<_, _>>();
    for members in classes.values_mut() {
        members.sort_unstable();
        for pair in members.chunks_exact(2) {
            targets.insert(pair[0], pair[1]);
            targets.insert(pair[1], pair[0]);
        }
    }
    targets
}

fn install_total(
    items: &[ItemId],
    generator: InputId,
    targets: &BTreeMap<ItemId, ItemId>,
    successors: &mut BTreeMap<(ItemId, InputId), ItemId>,
) {
    for item in items {
        successors.insert(
            (*item, generator),
            targets.get(item).copied().unwrap_or(*item),
        );
    }
}

fn generator_address(
    generator: InputId,
    species: TransportSpecies,
    targets: &BTreeMap<ItemId, ItemId>,
    family_by_item: &BTreeMap<ItemId, String>,
    inverse: Option<InputId>,
) -> TransportGeneratorAddress {
    let nonidentity_passages = targets
        .iter()
        .filter(|(source, target)| source != target)
        .map(|(source, target)| {
            (
                family_by_item[source].clone(),
                family_by_item[target].clone(),
            )
        })
        .collect::<Vec<_>>();
    let mut digest = Sha256::new();
    digest.update(b"athena-alpha/receiver-history-generator/v1");
    digest.update(generator.0.to_le_bytes());
    for (source, target) in &nonidentity_passages {
        digest.update((source.len() as u64).to_le_bytes());
        digest.update(source.as_bytes());
        digest.update((target.len() as u64).to_le_bytes());
        digest.update(target.as_bytes());
    }
    TransportGeneratorAddress {
        generator,
        occurrence: hex(digest.finalize().as_slice()),
        species,
        nonidentity_passages,
        exact_inverse_generator: inverse,
    }
}

fn message_key(message: &MessageAddress) -> (u32, u64, u64) {
    (message.container, message.record, message.visible_index)
}

pub(super) fn situated_message(message: &MessageAddress) -> String {
    format!(
        "{}:{}:{}:{}",
        message.container, message.record, message.visible_index, message.occurrence
    )
}

fn section_occurrence(aperture: &ContinuationAperture, family: &ContinuationFamily) -> String {
    let mut digest = Sha256::new();
    digest.update(b"athena-alpha/causal-section-occurrence/v1");
    digest.update(aperture.source_occurrence_sha256.octets());
    digest.update(family.prompt.container.to_le_bytes());
    digest.update(family.prompt.record.to_le_bytes());
    digest.update(family.prompt.visible_index.to_le_bytes());
    for response in &family.response {
        digest.update(response.container.to_le_bytes());
        digest.update(response.record.to_le_bytes());
        digest.update(response.visible_index.to_le_bytes());
    }
    hex(digest.finalize().as_slice())
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
