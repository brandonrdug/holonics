//! Parented cultivation from an addressed return over nominal boundaries.
//!
//! This owner is the missing edge between E2's provisional returned-codec candidate and durable
//! later conduct. It owns neither media kinds nor source material. A separately addressed return
//! binds at least two nominal boundary consequences to the candidate; the least durable delta is
//! the exact predecessor/successor state pivot with its complete boundary support. The existing
//! resident joint-transport law enacts predecessor, cultivated and locally withdrawn conduct.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    category::BoundaryId,
    cuda_refine::{CudaRefineExecutor, DeviceJointMediaTransport},
};

use super::heterogeneous_fusion::HeterogeneousFusionRest;

pub const BOUNDARY_CULTIVATION_SCHEMA: &str =
    "holonics.e3.returned-boundary-cultivation.v1";
const PROVISIONAL_SCHEMA: &str = "holonics.e2.provisional-returned-codec-candidate.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CandidateBoundaryContact {
    pub boundary: BoundaryId,
    pub anchor: u32,
    pub candidate_population: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProvisionalBoundaryCodecCandidate {
    pub schema: String,
    pub candidate_sha256: String,
    pub parent_codec_sha256: String,
    pub parent_boundary: BoundaryId,
    pub returned_boundary_contacts: Vec<CandidateBoundaryContact>,
    pub predecessor_occurrence_sha256: String,
    pub returned_occurrence_sha256: String,
    pub least_attributable_morphology: Vec<u32>,
    pub receiver_visible_defect: String,
    pub durable_learning_claimed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedBoundaryConsequence {
    pub boundary: BoundaryId,
    pub source_incidence_sha256: String,
    pub returned_consequence_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedBoundaryWorldReturn {
    pub occurrence_sha256: String,
    pub predecessor_occurrence_sha256: String,
    pub emission_occurrence_sha256: String,
    pub world_ordinal: u64,
    pub consequences: Vec<ReturnedBoundaryConsequence>,
    pub shared_consequence_sha256: String,
    pub exact_return_difference_sha256: String,
    pub separately_addressed_after_emission: bool,
}

impl AddressedBoundaryWorldReturn {
    pub fn found(
        predecessor_occurrence_sha256: String,
        emission_occurrence_sha256: String,
        world_ordinal: u64,
        consequences: Vec<ReturnedBoundaryConsequence>,
        shared_consequence_sha256: String,
    ) -> Result<Self, BoundaryCultivationRefusal> {
        if world_ordinal == 0
            || !valid_digest(&predecessor_occurrence_sha256)
            || !valid_digest(&emission_occurrence_sha256)
            || !valid_digest(&shared_consequence_sha256)
        {
            return Err(BoundaryCultivationRefusal::Return);
        }
        validate_consequences(&consequences)?;
        let exact_return_difference_sha256 = digest_json(&(
            &predecessor_occurrence_sha256,
            &emission_occurrence_sha256,
            world_ordinal,
            &consequences,
            &shared_consequence_sha256,
        ))?;
        let occurrence_sha256 = digest_json(&(
            &predecessor_occurrence_sha256,
            &exact_return_difference_sha256,
            world_ordinal,
        ))?;
        Ok(Self {
            occurrence_sha256,
            predecessor_occurrence_sha256,
            emission_occurrence_sha256,
            world_ordinal,
            consequences,
            shared_consequence_sha256,
            exact_return_difference_sha256,
            separately_addressed_after_emission: true,
        })
    }

    fn validate(&self) -> Result<(), BoundaryCultivationRefusal> {
        let rebuilt = Self::found(
            self.predecessor_occurrence_sha256.clone(),
            self.emission_occurrence_sha256.clone(),
            self.world_ordinal,
            self.consequences.clone(),
            self.shared_consequence_sha256.clone(),
        )?;
        if &rebuilt != self || !self.separately_addressed_after_emission {
            return Err(BoundaryCultivationRefusal::Return);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryRestIdentity {
    pub standing_sha256: String,
    pub decoder_sha256: String,
    pub fibres_sha256: String,
    pub complete_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ParentedBoundaryDelta {
    pub candidate_sha256: String,
    pub parent_codec_sha256: String,
    pub parent_boundary: BoundaryId,
    pub predecessor_state: u32,
    pub successor_state: u32,
    pub support_boundaries: Vec<BoundaryId>,
    pub least_attributable_morphology: Vec<u32>,
    pub exact_rank: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContinuationSibling {
    pub committed: bool,
    pub identity_sha256: String,
    pub decision_occurrence_sha256: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedBoundaryCultivationStanding {
    pub schema: String,
    pub predecessor: BoundaryRestIdentity,
    pub returned: AddressedBoundaryWorldReturn,
    pub delta: ParentedBoundaryDelta,
    pub declined_sibling: ContinuationSibling,
    pub committed_sibling: ContinuationSibling,
    pub reconstruction_fibre: String,
    pub open_exterior: Vec<String>,
}

/// One continuing ecology. It is deliberately not `Clone`.
#[derive(Debug, PartialEq, Eq)]
pub struct ReturnedBoundaryCultivationRest {
    predecessor: HeterogeneousFusionRest,
    standing: ReturnedBoundaryCultivationStanding,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryCultivationWithdrawal {
    pub cultivated_identity_sha256: String,
    pub declared_predecessor_sha256: String,
    pub restored_predecessor_sha256: String,
    pub exact_predecessor_restored: bool,
}

impl ReturnedBoundaryCultivationRest {
    pub fn cultivate(
        predecessor: HeterogeneousFusionRest,
        provisional_bytes: &[u8],
        returned: AddressedBoundaryWorldReturn,
    ) -> Result<Self, BoundaryCultivationRefusal> {
        predecessor
            .validate()
            .map_err(|error| BoundaryCultivationRefusal::Predecessor(error.to_string()))?;
        let provisional: ProvisionalBoundaryCodecCandidate =
            serde_json::from_slice(provisional_bytes)
                .map_err(|error| BoundaryCultivationRefusal::Wire(error.to_string()))?;
        validate_candidate(&predecessor, &provisional)?;
        returned.validate()?;
        if returned.predecessor_occurrence_sha256 != provisional.returned_occurrence_sha256 {
            return Err(BoundaryCultivationRefusal::Lineage);
        }
        let admitted = predecessor
            .standing
            .ports
            .iter()
            .map(|port| port.boundary)
            .collect::<BTreeSet<_>>();
        let support = returned
            .consequences
            .iter()
            .map(|consequence| consequence.boundary)
            .collect::<BTreeSet<_>>();
        if support.len() < 2
            || !support.is_subset(&admitted)
            || !support.contains(&provisional.parent_boundary)
        {
            return Err(BoundaryCultivationRefusal::Boundary);
        }
        let predecessor_identity = rest_identity(&predecessor)?;
        let delta = ParentedBoundaryDelta {
            candidate_sha256: provisional.candidate_sha256.clone(),
            parent_codec_sha256: provisional.parent_codec_sha256.clone(),
            parent_boundary: provisional.parent_boundary,
            predecessor_state: predecessor.standing.shared_generator.predecessor,
            successor_state: predecessor.standing.shared_generator.successor,
            support_boundaries: support.into_iter().collect(),
            least_attributable_morphology: provisional.least_attributable_morphology.clone(),
            exact_rank: 1,
        };
        let declined_sibling = ContinuationSibling {
            committed: false,
            identity_sha256: digest_json(&(
                &predecessor_identity.complete_sha256,
                &provisional.candidate_sha256,
                "declined",
            ))?,
            decision_occurrence_sha256: None,
        };
        let committed_sibling = ContinuationSibling {
            committed: true,
            identity_sha256: digest_json(&(
                &predecessor_identity.complete_sha256,
                &provisional.candidate_sha256,
                &returned.occurrence_sha256,
                &delta,
            ))?,
            decision_occurrence_sha256: Some(returned.occurrence_sha256.clone()),
        };
        let rest = Self {
            predecessor,
            standing: ReturnedBoundaryCultivationStanding {
                schema: BOUNDARY_CULTIVATION_SCHEMA.to_owned(),
                predecessor: predecessor_identity,
                returned,
                delta,
                declined_sibling,
                committed_sibling,
                reconstruction_fibre: "withdrawing the parented delta restores the exact predecessor components; withdrawing any supporting boundary retains the corresponding E2 directional defect".to_owned(),
                open_exterior: vec![
                    "successor histories not exposed by the returned nominal-boundary family remain open".to_owned(),
                    "unknown-carrier codec induction remains outside this cultivation".to_owned(),
                ],
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        standing: &[u8],
        decoder: &[u8],
        fibres: &[u8],
        cultivation: &[u8],
    ) -> Result<Self, BoundaryCultivationRefusal> {
        let predecessor = HeterogeneousFusionRest::read(standing, decoder, fibres)
            .map_err(|error| BoundaryCultivationRefusal::Predecessor(error.to_string()))?;
        let standing = serde_json::from_slice(cultivation)
            .map_err(|error| BoundaryCultivationRefusal::Wire(error.to_string()))?;
        let rest = Self {
            predecessor,
            standing,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing(&self) -> &ReturnedBoundaryCultivationStanding {
        &self.standing
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, BoundaryCultivationRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.standing)
            .map_err(|error| BoundaryCultivationRefusal::Wire(error.to_string()))
    }

    pub fn canonical_identity(&self) -> Result<String, BoundaryCultivationRefusal> {
        digest_json(&(
            rest_identity(&self.predecessor)?,
            &self.standing,
        ))
    }

    pub fn conduct_predecessor(
        &self,
        candidate_counts: &[u32],
        card: &mut CudaRefineExecutor,
    ) -> Result<DeviceJointMediaTransport, BoundaryCultivationRefusal> {
        self.conduct(candidate_counts, self.standing.delta.predecessor_state, card)
    }

    pub fn conduct_cultivated(
        &self,
        candidate_counts: &[u32],
        card: &mut CudaRefineExecutor,
    ) -> Result<DeviceJointMediaTransport, BoundaryCultivationRefusal> {
        self.conduct(candidate_counts, self.standing.delta.successor_state, card)
    }

    pub fn withdraw(
        self,
    ) -> Result<(HeterogeneousFusionRest, BoundaryCultivationWithdrawal), BoundaryCultivationRefusal>
    {
        self.validate()?;
        let cultivated_identity_sha256 = self.canonical_identity()?;
        let restored = rest_identity(&self.predecessor)?;
        let receipt = BoundaryCultivationWithdrawal {
            cultivated_identity_sha256,
            declared_predecessor_sha256: self.standing.predecessor.complete_sha256.clone(),
            restored_predecessor_sha256: restored.complete_sha256.clone(),
            exact_predecessor_restored: restored == self.standing.predecessor,
        };
        if !receipt.exact_predecessor_restored {
            return Err(BoundaryCultivationRefusal::Reconstruction);
        }
        Ok((self.predecessor, receipt))
    }

    fn conduct(
        &self,
        candidate_counts: &[u32],
        state: u32,
        card: &mut CudaRefineExecutor,
    ) -> Result<DeviceJointMediaTransport, BoundaryCultivationRefusal> {
        self.validate()?;
        let anchors = self.standing.delta.least_attributable_morphology.len();
        if candidate_counts.len() != anchors * self.predecessor.standing.ports.len()
            || candidate_counts.contains(&0)
        {
            return Err(BoundaryCultivationRefusal::Candidate);
        }
        card.conduct_joint_media_transport_on_device(
            candidate_counts,
            anchors,
            &[state, state],
            &self.predecessor.decoder_addresses(),
            &self.predecessor.starts(),
            self.predecessor.standing.family_count as usize,
            self.predecessor.standing.ports.len(),
        )
        .map_err(|error| BoundaryCultivationRefusal::Apparatus(error.to_string()))
    }

    fn validate(&self) -> Result<(), BoundaryCultivationRefusal> {
        self.predecessor
            .validate()
            .map_err(|error| BoundaryCultivationRefusal::Predecessor(error.to_string()))?;
        self.standing.returned.validate()?;
        let predecessor = rest_identity(&self.predecessor)?;
        let boundaries = self
            .predecessor
            .standing
            .ports
            .iter()
            .map(|port| port.boundary)
            .collect::<BTreeSet<_>>();
        let support = self
            .standing
            .delta
            .support_boundaries
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let expected_declined = digest_json(&(
            &predecessor.complete_sha256,
            &self.standing.delta.candidate_sha256,
            "declined",
        ))?;
        let expected_committed = digest_json(&(
            &predecessor.complete_sha256,
            &self.standing.delta.candidate_sha256,
            &self.standing.returned.occurrence_sha256,
            &self.standing.delta,
        ))?;
        if self.standing.schema != BOUNDARY_CULTIVATION_SCHEMA
            || self.standing.predecessor != predecessor
            || self.standing.delta.predecessor_state
                != self.predecessor.standing.shared_generator.predecessor
            || self.standing.delta.successor_state
                != self.predecessor.standing.shared_generator.successor
            || self.standing.delta.predecessor_state == self.standing.delta.successor_state
            || self.standing.delta.exact_rank != 1
            || self.standing.delta.least_attributable_morphology.is_empty()
            || support.len() < 2
            || !support.is_subset(&boundaries)
            || !support.contains(&self.standing.delta.parent_boundary)
            || self.standing.declined_sibling.committed
            || self.standing.declined_sibling.identity_sha256 != expected_declined
            || self.standing.declined_sibling.decision_occurrence_sha256.is_some()
            || !self.standing.committed_sibling.committed
            || self.standing.committed_sibling.identity_sha256 != expected_committed
            || self.standing.committed_sibling.decision_occurrence_sha256.as_deref()
                != Some(&self.standing.returned.occurrence_sha256)
            || !valid_digest(&self.standing.delta.candidate_sha256)
            || !valid_digest(&self.standing.delta.parent_codec_sha256)
            || self.standing.open_exterior.is_empty()
        {
            return Err(BoundaryCultivationRefusal::Standing);
        }
        Ok(())
    }
}

fn validate_candidate(
    predecessor: &HeterogeneousFusionRest,
    candidate: &ProvisionalBoundaryCodecCandidate,
) -> Result<(), BoundaryCultivationRefusal> {
    let boundaries = predecessor
        .standing
        .ports
        .iter()
        .map(|port| port.boundary)
        .collect::<BTreeSet<_>>();
    let anchors = candidate
        .returned_boundary_contacts
        .iter()
        .map(|contact| contact.anchor)
        .collect::<BTreeSet<_>>();
    if candidate.schema != PROVISIONAL_SCHEMA
        || candidate.durable_learning_claimed
        || !valid_digest(&candidate.candidate_sha256)
        || !valid_digest(&candidate.parent_codec_sha256)
        || !valid_digest(&candidate.predecessor_occurrence_sha256)
        || !valid_digest(&candidate.returned_occurrence_sha256)
        || !boundaries.contains(&candidate.parent_boundary)
        || candidate.receiver_visible_defect.is_empty()
        || candidate.returned_boundary_contacts.is_empty()
        || candidate
            .returned_boundary_contacts
            .iter()
            .any(|contact| {
                !boundaries.contains(&contact.boundary) || contact.candidate_population == 0
            })
        || anchors.len() != candidate.least_attributable_morphology.len()
        || rest_identity(predecessor)?.complete_sha256
            != candidate.predecessor_occurrence_sha256
    {
        return Err(BoundaryCultivationRefusal::Candidate);
    }
    Ok(())
}

fn validate_consequences(
    consequences: &[ReturnedBoundaryConsequence],
) -> Result<(), BoundaryCultivationRefusal> {
    let boundaries = consequences
        .iter()
        .map(|consequence| consequence.boundary)
        .collect::<BTreeSet<_>>();
    if consequences.len() < 2
        || boundaries.len() != consequences.len()
        || consequences.iter().any(|consequence| {
            !valid_digest(&consequence.source_incidence_sha256)
                || !valid_digest(&consequence.returned_consequence_sha256)
        })
    {
        return Err(BoundaryCultivationRefusal::Boundary);
    }
    Ok(())
}

fn rest_identity(
    rest: &HeterogeneousFusionRest,
) -> Result<BoundaryRestIdentity, BoundaryCultivationRefusal> {
    let standing = rest
        .standing_bytes()
        .map_err(|error| BoundaryCultivationRefusal::Predecessor(error.to_string()))?;
    let decoder = rest
        .decoder_bytes()
        .map_err(|error| BoundaryCultivationRefusal::Predecessor(error.to_string()))?;
    let fibres = rest
        .fibre_bytes()
        .map_err(|error| BoundaryCultivationRefusal::Predecessor(error.to_string()))?;
    Ok(BoundaryRestIdentity {
        standing_sha256: digest(&standing),
        decoder_sha256: digest(&decoder),
        fibres_sha256: digest(&fibres),
        complete_sha256: digest_many(&[&standing, &decoder, &fibres]),
    })
}

fn digest_json(value: &impl Serialize) -> Result<String, BoundaryCultivationRefusal> {
    serde_json::to_vec(value)
        .map(|bytes| digest(&bytes))
        .map_err(|error| BoundaryCultivationRefusal::Wire(error.to_string()))
}

fn digest_many(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    format!("{:x}", digest.finalize())
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn valid_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum BoundaryCultivationRefusal {
    #[error("the predecessor nominal-boundary rest refused: {0}")]
    Predecessor(String),
    #[error("the provisional codec candidate refused")]
    Candidate,
    #[error("the returned nominal-boundary occurrence refused")]
    Return,
    #[error("the returned occurrence left the addressed predecessor lineage")]
    Lineage,
    #[error("the returned boundary support refused")]
    Boundary,
    #[error("the cultivated standing moved")]
    Standing,
    #[error("the cultivation reconstruction fibre did not restore its predecessor")]
    Reconstruction,
    #[error("resident apparatus refused cultivation conduct: {0}")]
    Apparatus(String),
    #[error("boundary cultivation wire refused: {0}")]
    Wire(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::phoenix::heterogeneous_fusion::{
        PortDeclaration, SharedWorldGenerator, SourcePortResponse,
    };

    const OPTICAL: BoundaryId = BoundaryId(101);
    const ACOUSTIC: BoundaryId = BoundaryId(103);
    const PARENT: BoundaryId = BoundaryId(109);

    fn mark(value: u32) -> String {
        format!("{value:064x}")
    }

    fn predecessor() -> HeterogeneousFusionRest {
        let boundaries = [OPTICAL, ACOUSTIC, PARENT];
        let ports = boundaries
            .iter()
            .map(|boundary| PortDeclaration {
                boundary: *boundary,
                source_boundary: format!("source-{}", boundary.0),
                source_population: "lineage only".to_owned(),
                source_extent: 1,
                incidence: format!("incidence-{}", boundary.0),
            })
            .collect();
        let mut responses = Vec::new();
        let mut value = 10;
        for family in 0..2 {
            for boundary in boundaries {
                for state in 0..2 {
                    responses.push(SourcePortResponse {
                        family,
                        state,
                        boundary,
                        occurrence: format!("occurrence/{family}/{}/{state}", boundary.0),
                        occurrence_sha256: mark(value),
                        consequence_sha256: mark(value + 1),
                        incidence_sha256: mark(value + 2),
                        semantic_units: 1,
                    });
                    value += 3;
                }
            }
        }
        HeterogeneousFusionRest::found(
            mark(1),
            ports,
            responses,
            SharedWorldGenerator {
                name: "returned orientation".to_owned(),
                predecessor: 0,
                successor: 1,
                lineage: "addressed lineage".to_owned(),
                common_world_receiver: "complete boundary receiver".to_owned(),
            },
            vec!["unmounted aperture".to_owned()],
            vec!["open successor".to_owned()],
        )
        .expect("predecessor")
    }

    fn candidate(predecessor: &HeterogeneousFusionRest) -> Vec<u8> {
        let candidate = ProvisionalBoundaryCodecCandidate {
            schema: PROVISIONAL_SCHEMA.to_owned(),
            candidate_sha256: mark(80),
            parent_codec_sha256: mark(81),
            parent_boundary: PARENT,
            returned_boundary_contacts: [OPTICAL, ACOUSTIC, PARENT]
                .into_iter()
                .flat_map(|boundary| {
                    (0..2).map(move |anchor| CandidateBoundaryContact {
                        boundary,
                        anchor,
                        candidate_population: 1,
                    })
                })
                .collect(),
            predecessor_occurrence_sha256: rest_identity(predecessor)
                .expect("identity")
                .complete_sha256,
            returned_occurrence_sha256: mark(82),
            least_attributable_morphology: vec![1, 1],
            receiver_visible_defect: "directional withdrawal".to_owned(),
            durable_learning_claimed: false,
        };
        serde_json::to_vec(&candidate).expect("candidate")
    }

    fn returning() -> AddressedBoundaryWorldReturn {
        AddressedBoundaryWorldReturn::found(
            mark(82),
            mark(83),
            1,
            [OPTICAL, ACOUSTIC, PARENT]
                .into_iter()
                .enumerate()
                .map(|(at, boundary)| ReturnedBoundaryConsequence {
                    boundary,
                    source_incidence_sha256: mark(90 + at as u32),
                    returned_consequence_sha256: mark(100 + at as u32),
                })
                .collect(),
            mark(110),
        )
        .expect("return")
    }

    #[test]
    fn returned_candidate_rests_and_withdraws_to_the_exact_predecessor() {
        let base = predecessor();
        let standing = base.standing_bytes().expect("standing");
        let decoder = base.decoder_bytes().expect("decoder");
        let fibres = base.fibre_bytes().expect("fibres");
        let candidate = candidate(&base);
        let cultivated = ReturnedBoundaryCultivationRest::cultivate(
            base,
            &candidate,
            returning(),
        )
        .expect("cultivated");
        assert_ne!(
            cultivated.standing.declined_sibling.identity_sha256,
            cultivated.standing.committed_sibling.identity_sha256
        );
        let bytes = cultivated.standing_bytes().expect("cultivation standing");
        let remounted = ReturnedBoundaryCultivationRest::read(
            &standing, &decoder, &fibres, &bytes,
        )
        .expect("remounted");
        let (_, withdrawal) = remounted.withdraw().expect("withdrawal");
        assert!(withdrawal.exact_predecessor_restored);
    }

    #[test]
    fn one_returned_boundary_cannot_found_the_cultivation() {
        let base = predecessor();
        let candidate = candidate(&base);
        let one = AddressedBoundaryWorldReturn::found(
            mark(82),
            mark(83),
            1,
            vec![ReturnedBoundaryConsequence {
                boundary: PARENT,
                source_incidence_sha256: mark(90),
                returned_consequence_sha256: mark(100),
            }],
            mark(110),
        );
        assert_eq!(one, Err(BoundaryCultivationRefusal::Boundary));
        assert!(ReturnedBoundaryCultivationRest::cultivate(base, &candidate, returning()).is_ok());
    }
}
