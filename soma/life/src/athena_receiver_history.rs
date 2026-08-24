//! Athena alpha's receiver/history congruence.
//!
//! The source states are addressed causal sections. Exact returned surfaces are receiver faces;
//! they are never identities. The native state is the coarsest quotient stable under every
//! admitted transport generator, complete fibres remain attached, and source roles are relations
//! to one proposal rather than a global partition.

mod roles;
mod system;
mod types;

use std::collections::BTreeMap;

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    receiver_exact_compression::{compress, compress_on_device, ItemId, ObservedSystem},
    receiver_history_compression::ReceiverHistoryCompression,
};

use crate::exchange_world_tube::ContinuationAperture;

pub use types::{
    AthenaReceiverHistoryCongruence, CausalSectionAddress, ProposalRelationKind,
    ProposalRoleIncidence, ReceiverGrain, RelationTargetFace, ResidentQuotientReceipt,
    SurfaceOnlyCounterexample, TransportGeneratorAddress, TransportSpecies,
};

use system::LaboratorySections;

impl AthenaReceiverHistoryCongruence {
    pub fn found_on_device(
        aperture: &ContinuationAperture,
        executor: &mut CudaRefineExecutor,
    ) -> Result<Self, String> {
        let sections = LaboratorySections::found(aperture)?;
        let surface = sections.surface_view();
        let surface_exact = compress(&surface);
        let rich = sections.rich_view();
        let reference = compress(&rich);
        let launches_before = executor.launches();
        let exact = compress_on_device(&rich, executor).map_err(|error| error.to_string())?;
        if reference != exact {
            return Err("resident and reference receiver-history quotients disagree".to_owned());
        }
        let native =
            ReceiverHistoryCompression::found(&rich, &exact).map_err(|error| error.to_string())?;
        let counterexamples =
            surface_counterexamples(&sections, &surface, &surface_exact, &rich, &native)?;
        if counterexamples.is_empty() {
            return Err("the surface-only quotient returned no constructive falsifier".to_owned());
        }
        let proposal_roles = roles::derive(aperture, &sections);
        let overlapping_role_population = overlapping_roles(&proposal_roles);
        if overlapping_role_population == 0 {
            return Err(
                "proposal-relative roles collapsed back into one global partition".to_owned(),
            );
        }
        let resident = ResidentQuotientReceipt {
            schema: "soma-life.athena-receiver-history-resident-quotient.v1".to_owned(),
            device: executor.device_name().to_owned(),
            block_threads: executor.block_threads(),
            warp_size: executor.warp_size(),
            launches: executor.launches().saturating_sub(launches_before),
            source_states: exact.conduct.items_in_order().len(),
            receiver_grains: rich.receivers().len(),
            transport_generators: rich.inputs().len(),
            one_shot_classes: exact.one_shot.len(),
            receiver_history_classes: exact.conduct.len(),
            memory_order: exact.memory_order(),
            cpu_device_partition_equal: true,
            cpu_semantic_replay_after_device: false,
        };
        let product = Self {
            schema: "soma-life.athena-receiver-history-congruence.v1".to_owned(),
            source_occurrence_sha256: aperture.source_occurrence_sha256.render(),
            receivers: vec![
                ReceiverGrain::ReturnedSurface,
                ReceiverGrain::BoundaryIncidence,
                ReceiverGrain::WorldConsequence,
                ReceiverGrain::ContinuationPort,
            ],
            sections: sections.sections,
            transport_generators: sections.generators,
            proposal_roles,
            exact,
            native,
            surface_only_counterexamples: counterexamples,
            resident,
            open_fibres: vec![
                "candidate emission and sibling reveal remain the next addressed passage"
                    .to_owned(),
                "the quotient retains source occurrences in complete reconstruction fibres"
                    .to_owned(),
            ],
        };
        product.validate()?;
        Ok(product)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, String> {
        let product: Self = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
        product.validate()?;
        Ok(product)
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.schema != "soma-life.athena-receiver-history-congruence.v1"
            || self.sections.is_empty()
            || self.receivers.len() != self.resident.receiver_grains
            || self.transport_generators.len() != self.resident.transport_generators
            || self.surface_only_counterexamples.is_empty()
            || !self.resident.cpu_device_partition_equal
            || self.resident.cpu_semantic_replay_after_device
        {
            return Err("receiver-history congruence receipt is incomplete".to_owned());
        }
        self.native.validate().map_err(|error| error.to_string())?;
        if self.native.source_population.len() != self.sections.len()
            || self.native.reconstruction_fibres.len() != self.exact.conduct.len()
            || self.native.generators.len() != self.transport_generators.len()
            || self.resident.memory_order != self.exact.memory_order()
        {
            return Err("native quotient, fibres, generators, or memory face disagree".to_owned());
        }
        let sources = self
            .native
            .reconstruction_fibres
            .iter()
            .flat_map(|fibre| fibre.sources.iter().copied())
            .collect::<Vec<_>>();
        if sources.len() != self.sections.len() {
            return Err(
                "the complete source population did not return through the fibres".to_owned(),
            );
        }
        Ok(())
    }
}

fn surface_counterexamples(
    sections: &LaboratorySections,
    surface: &dyn ObservedSystem,
    surface_exact: &holonic_engine::receiver_exact_compression::ReceiverExactCompression,
    rich: &dyn ObservedSystem,
    native: &ReceiverHistoryCompression,
) -> Result<Vec<SurfaceOnlyCounterexample>, String> {
    let collapsed = surface_exact
        .collapsed
        .iter()
        .map(|pair| ((pair.left, pair.right), pair))
        .collect::<BTreeMap<_, _>>();
    let surface_receiver = ReceiverGrain::ReturnedSurface.id();
    let mut by_surface = BTreeMap::<u64, Vec<ItemId>>::new();
    for item in surface.items() {
        by_surface
            .entry(surface.observation(item, surface_receiver).0)
            .or_default()
            .push(item);
    }
    let generator_occurrence = sections
        .generators
        .iter()
        .map(|generator| (generator.generator, generator.occurrence.as_str()))
        .collect::<BTreeMap<_, _>>();
    let mut out = Vec::new();
    for members in by_surface.values() {
        for (at, left) in members.iter().enumerate() {
            for right in &members[at + 1..] {
                if native.encode(*left).map_err(|error| error.to_string())?
                    == native.encode(*right).map_err(|error| error.to_string())?
                {
                    continue;
                }
                let richer = rich.receivers().into_iter().find(|receiver| {
                    rich.observation(*left, *receiver) != rich.observation(*right, *receiver)
                });
                let pair = collapsed.get(&(*left, *right));
                let word = pair
                    .map(|pair| {
                        pair.distinguishing_word
                            .iter()
                            .map(|input| generator_occurrence[input].to_owned())
                            .collect()
                    })
                    .unwrap_or_default();
                let witness = richer
                    .map(|receiver| {
                        (
                            receiver_grain(receiver),
                            rich.observation(*left, receiver).0,
                            rich.observation(*right, receiver).0,
                        )
                    })
                    .or_else(|| {
                        pair.and_then(|pair| pair.witness)
                            .map(|(receiver, left, right)| {
                                (receiver_grain(receiver), left.0, right.0)
                            })
                    });
                let surface_sha = &sections.sections[left.0 as usize].returned_surface_sha256;
                out.push(SurfaceOnlyCounterexample {
                    left_family: sections.family_by_item[left].clone(),
                    right_family: sections.family_by_item[right].clone(),
                    equal_returned_surface_sha256: surface_sha.clone(),
                    separating_receiver: witness.map(|witness| witness.0),
                    shortest_ordered_word: word,
                    separated_by_terminus: pair.is_some_and(|pair| pair.separated_by_terminus),
                    left_face: witness.map(|witness| witness.1),
                    right_face: witness.map(|witness| witness.2),
                });
            }
        }
    }
    out.sort_by(|left, right| {
        (&left.left_family, &left.right_family).cmp(&(&right.left_family, &right.right_family))
    });
    Ok(out)
}

fn receiver_grain(
    receiver: holonic_engine::receiver_exact_compression::ReceiverId,
) -> ReceiverGrain {
    match receiver.0 {
        0 => ReceiverGrain::ReturnedSurface,
        1 => ReceiverGrain::BoundaryIncidence,
        2 => ReceiverGrain::WorldConsequence,
        _ => ReceiverGrain::ContinuationPort,
    }
}

fn overlapping_roles(roles: &[ProposalRoleIncidence]) -> usize {
    let mut targets = BTreeMap::<(&str, &str), usize>::new();
    for role in roles {
        *targets
            .entry((role.proposal.as_str(), role.target.as_str()))
            .or_default() += 1;
    }
    targets
        .values()
        .filter(|population| **population > 1)
        .count()
}
