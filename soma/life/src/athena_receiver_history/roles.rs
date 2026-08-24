use std::collections::BTreeSet;

use holonic_engine::receiver_exact_compression::{InputId, ItemId};
use sha2::{Digest, Sha256};

use crate::exchange_world_tube::ContinuationAperture;

use super::{
    system::{situated_message, LaboratorySections},
    types::{ProposalRelationKind, ProposalRoleIncidence, RelationTargetFace, TransportSpecies},
};

pub(super) fn derive(
    aperture: &ContinuationAperture,
    sections: &LaboratorySections,
) -> Vec<ProposalRoleIncidence> {
    let exterior = sections
        .generators
        .iter()
        .find(|generator| generator.species == TransportSpecies::ExteriorReturn)
        .map(|generator| generator.generator)
        .unwrap_or(InputId(0));
    let rebase = sections
        .generators
        .iter()
        .find(|generator| generator.species == TransportSpecies::ExactRebase)
        .map(|generator| generator.generator)
        .unwrap_or(InputId(1));
    let mut roles = Vec::new();
    for item in &sections.items {
        let proposal = &sections.family_by_item[item];
        let family = &aperture.families[sections.aperture_family_by_item[item]];
        push(
            &mut roles,
            proposal,
            ProposalRelationKind::Development,
            proposal,
            RelationTargetFace::Family,
            "the proposal is founded by its own addressed history occurrence",
        );
        for response in &family.response {
            push(
                &mut roles,
                proposal,
                ProposalRelationKind::Sibling,
                &situated_message(response),
                RelationTargetFace::Message,
                "the response occurrence is later sibling testimony and is not candidate input",
            );
        }

        let later = sections.successor(*item, exterior);
        if later != *item {
            let target = &sections.family_by_item[&later];
            push(
                &mut roles,
                proposal,
                ProposalRelationKind::HeldOut,
                target,
                RelationTargetFace::Family,
                "the exterior-return passage reaches this family only after the proposal boundary",
            );
            let response_support = family
                .response
                .iter()
                .map(situated_message)
                .collect::<BTreeSet<_>>();
            if sections.supports[&later]
                .iter()
                .any(|occurrence| response_support.contains(occurrence))
            {
                push(
                    &mut roles,
                    proposal,
                    ProposalRelationKind::Revisit,
                    target,
                    RelationTargetFace::Family,
                    "later current re-enters support carried by the proposal response",
                );
            }
        }

        let rebased = sections.successor(*item, rebase);
        if rebased != *item {
            push(
                &mut roles,
                proposal,
                ProposalRelationKind::Rebase,
                &sections.family_by_item[&rebased],
                RelationTargetFace::Family,
                "the exact response face is shared and the involutive chart transport returns both identity compositions",
            );
        }

        if let Some(control) = independent_control(*item, exterior, sections) {
            push(
                &mut roles,
                proposal,
                ProposalRelationKind::Control,
                &sections.family_by_item[&control],
                RelationTargetFace::Family,
                "the two addressed supports and their exterior-return endpoints are disjoint, so their local passages interchange exactly",
            );
        }
    }
    roles.sort_by(|left, right| {
        (&left.proposal, left.relation, &left.target).cmp(&(
            &right.proposal,
            right.relation,
            &right.target,
        ))
    });
    roles
}

fn independent_control(
    proposal: ItemId,
    exterior: InputId,
    sections: &LaboratorySections,
) -> Option<ItemId> {
    let proposal_target = sections.successor(proposal, exterior);
    let proposal_endpoints = BTreeSet::from([proposal, proposal_target]);
    sections.items.iter().copied().find(|candidate| {
        if *candidate == proposal
            || !sections.supports[&proposal].is_disjoint(&sections.supports[candidate])
        {
            return false;
        }
        let candidate_target = sections.successor(*candidate, exterior);
        let candidate_endpoints = BTreeSet::from([*candidate, candidate_target]);
        proposal_endpoints.is_disjoint(&candidate_endpoints)
            && local_passages_commute(
                proposal,
                proposal_target,
                *candidate,
                candidate_target,
                &sections.items,
            )
    })
}

fn local_passages_commute(
    left: ItemId,
    left_target: ItemId,
    right: ItemId,
    right_target: ItemId,
    population: &[ItemId],
) -> bool {
    let step = |item: ItemId, source: ItemId, target: ItemId| {
        if item == source {
            target
        } else {
            item
        }
    };
    population.iter().all(|item| {
        step(step(*item, right, right_target), left, left_target)
            == step(step(*item, left, left_target), right, right_target)
    })
}

fn push(
    roles: &mut Vec<ProposalRoleIncidence>,
    proposal: &str,
    relation: ProposalRelationKind,
    target: &str,
    target_face: RelationTargetFace,
    witness: &str,
) {
    let mut digest = Sha256::new();
    digest.update(b"athena-alpha/proposal-role-incidence/v1");
    digest.update((proposal.len() as u64).to_le_bytes());
    digest.update(proposal.as_bytes());
    digest.update([relation as u8]);
    digest.update((target.len() as u64).to_le_bytes());
    digest.update(target.as_bytes());
    roles.push(ProposalRoleIncidence {
        proposal: proposal.to_owned(),
        relation,
        target: target.to_owned(),
        target_face,
        addressed_lineage: hex(digest.finalize().as_slice()),
        witness: witness.to_owned(),
    });
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
