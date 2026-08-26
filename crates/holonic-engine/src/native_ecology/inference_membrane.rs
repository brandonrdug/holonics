//! One native request/return membrane over the cultivated nominal-boundary Athena body.
//!
//! Exterior endpoint names, messages, roles, chunks and media labels do not enter this owner. A
//! request is one addressed occurrence at a nominal boundary with its caused incidence population.
//! A co-present request front conducts in one CUDA launch, then each member receives its own
//! addressed continuation delta and complete receiver-relative fibre. The product body is owned
//! once; branches retain only their local immutable differences.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::CausalMembrane;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    category::BoundaryId,
    cuda_refine::CudaRefineExecutor,
    interchange::{FrontCertificate, MemberFootprint, certify_footprints},
    native_ecology::heterogeneous_fusion::BoundaryReconstructionFibre,
};

use super::boundary_cultivation::{BoundaryCultivationRefusal, ReturnedBoundaryCultivationRest};

const STANDING_SCHEMA: &str = "holonic-engine.native-ecology.native-inference-membrane.v1";

/// A caused native occurrence. Numerical population is entering incidence, not authored capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeBoundaryOccurrence {
    pub occurrence_sha256: String,
    pub predecessor_continuation_sha256: String,
    pub boundary: BoundaryId,
    pub source_incidence_sha256: String,
    pub lineage_sha256: String,
    pub candidate_population: Vec<u32>,
    pub receiver_boundaries: Vec<BoundaryId>,
    pub frontier_aperture: usize,
}

/// One addressed occurrence in the returned causal frontier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFrontierOccurrence {
    pub ordinal: u32,
    pub predecessor_sha256: String,
    pub incidence_sha256: String,
    pub consequence_sha256: String,
    pub address_sha256: String,
}

/// Complete native reconstruction testimony for one requested boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeReceiverFibre {
    pub boundary: BoundaryId,
    pub members: Vec<BoundaryReconstructionFibre>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeExactWork {
    pub entering_cells: u64,
    pub resident_cells: u64,
    pub returned_cells: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeApparatusReceipt {
    pub launches: u64,
    pub synchronizations: u64,
    pub active_lanes: u32,
    pub resident_octets: u64,
    pub transfer_octets: u64,
}

/// The native potential-complex consequence before any compatibility projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePotentialConsequence {
    pub boundary: BoundaryId,
    pub receiver_boundaries: Vec<BoundaryId>,
    pub joint_anchor: Vec<u32>,
    pub shared_withdrawn_joint_anchor: Vec<u32>,
    pub local_withdrawn_joint_anchor: Vec<u32>,
    pub predecessor_consequence: Vec<u32>,
    pub cultivated_consequence: Vec<u32>,
    pub shared_withdrawn_consequence: Vec<u32>,
    pub local_withdrawn_consequence: Vec<u32>,
    pub reconstruction_fibres: Vec<NativeReceiverFibre>,
    pub exact_work: NativeExactWork,
    pub apparatus: NativeApparatusReceipt,
    pub open_exterior: Vec<String>,
}

/// One immutable local difference from an addressed predecessor. This is branch material, not a
/// copy of the ecology.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedContinuationDelta {
    pub predecessor_sha256: String,
    pub successor_sha256: String,
    pub entering_occurrence_sha256: String,
    pub boundary: BoundaryId,
    pub source_incidence_sha256: String,
    pub returned_consequence_sha256: String,
    pub frontier: Vec<NativeFrontierOccurrence>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeInferenceReturn {
    pub product_identity_sha256: String,
    pub continuation: AddressedContinuationDelta,
    pub consequence: NativePotentialConsequence,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeFrontReturn {
    pub members: Vec<NativeInferenceReturn>,
    pub interchange: FrontCertificate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthorizedContinuationWithdrawal {
    pub successor_sha256: String,
    pub predecessor_sha256: String,
    pub authorizing_occurrence_sha256: String,
    pub authorization_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeWithdrawalReturn {
    pub removed_successor_sha256: String,
    pub restored_predecessor_sha256: String,
    pub exact_local_withdrawal: bool,
}

/// Canonical detachable standing. It contains the root and local deltas, never request payloads.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeMembraneStanding {
    schema: String,
    product_identity_sha256: String,
    member_candidate_cells: usize,
    deltas: Vec<AddressedContinuationDelta>,
}

/// The one continuing product owner. Deliberately not `Clone`.
pub struct NativeInferenceMembrane {
    product: ReturnedBoundaryCultivationRest,
    product_identity_sha256: String,
    member_candidate_cells: usize,
    deltas: BTreeMap<String, AddressedContinuationDelta>,
    card: CudaRefineExecutor,
}

impl NativeInferenceMembrane {
    pub fn mount(
        product: ReturnedBoundaryCultivationRest,
        member_candidate_cells: usize,
        standing: Option<&[u8]>,
    ) -> Result<Self, NativeMembraneRefusal> {
        if member_candidate_cells == 0 {
            return Err(NativeMembraneRefusal::IncidenceShape);
        }
        let product_identity_sha256 = product
            .canonical_identity()
            .map_err(NativeMembraneRefusal::Cultivation)?;
        let mut deltas = BTreeMap::new();
        if let Some(bytes) = standing {
            let rested: NativeMembraneStanding = serde_json::from_slice(bytes)
                .map_err(|error| NativeMembraneRefusal::Rest(error.to_string()))?;
            if rested.schema != STANDING_SCHEMA
                || rested.product_identity_sha256 != product_identity_sha256
                || rested.member_candidate_cells != member_candidate_cells
            {
                return Err(NativeMembraneRefusal::RestIdentity);
            }
            let mut known = BTreeSet::from([product_identity_sha256.clone()]);
            for delta in rested.deltas {
                validate_delta(&delta)?;
                if !known.contains(&delta.predecessor_sha256)
                    || !known.insert(delta.successor_sha256.clone())
                {
                    return Err(NativeMembraneRefusal::RestLineage);
                }
                deltas.insert(delta.successor_sha256.clone(), delta);
            }
        }
        let card = CudaRefineExecutor::new()
            .map_err(|error| NativeMembraneRefusal::Apparatus(error.to_string()))?;
        Ok(Self {
            product,
            product_identity_sha256,
            member_candidate_cells,
            deltas,
            card,
        })
    }

    pub fn product_identity(&self) -> &str {
        &self.product_identity_sha256
    }

    pub fn rest_bytes(&self) -> Result<Vec<u8>, NativeMembraneRefusal> {
        let standing = NativeMembraneStanding {
            schema: STANDING_SCHEMA.to_owned(),
            product_identity_sha256: self.product_identity_sha256.clone(),
            member_candidate_cells: self.member_candidate_cells,
            deltas: ordered_deltas(&self.product_identity_sha256, &self.deltas)?,
        };
        serde_json::to_vec(&standing)
            .map_err(|error| NativeMembraneRefusal::Rest(error.to_string()))
    }

    pub fn receive_front(
        &mut self,
        occurrences: Vec<NativeBoundaryOccurrence>,
    ) -> Result<NativeFrontReturn, NativeMembraneRefusal> {
        if occurrences.is_empty() {
            return Err(NativeMembraneRefusal::EmptyFront);
        }
        let admitted = self
            .product
            .boundary_predecessor()
            .standing
            .ports
            .iter()
            .map(|port| port.boundary)
            .collect::<BTreeSet<_>>();
        let known = self.known_continuations();
        for occurrence in &occurrences {
            validate_occurrence(occurrence, self.member_candidate_cells, &admitted, &known)?;
        }
        let certificate = front_certificate(&occurrences, self.member_candidate_cells)?;
        if !certificate.is_interchangeable() {
            return Err(NativeMembraneRefusal::Interchange);
        }
        let candidate_population = occurrences
            .iter()
            .flat_map(|occurrence| occurrence.candidate_population.iter().copied())
            .collect::<Vec<_>>();
        let transport = self
            .product
            .conduct_cultivated_front(&candidate_population, occurrences.len(), &mut self.card)
            .map_err(NativeMembraneRefusal::Cultivation)?;
        if transport.launches != 1 || transport.synchronizations != 1 {
            return Err(NativeMembraneRefusal::Apparatus(
                "the co-present front did not return one resident launch and terminal synchronization"
                    .to_owned(),
            ));
        }
        let member_anchors = transport
            .anchors
            .checked_div(occurrences.len())
            .ok_or(NativeMembraneRefusal::IncidenceShape)?;
        let mut returns = Vec::with_capacity(occurrences.len());
        for (member, occurrence) in occurrences.into_iter().enumerate() {
            let from = member * member_anchors;
            let to = from + member_anchors;
            let local_from = from * transport.ports;
            let local_to = to * transport.ports;
            let joint = transport.joint_anchor[from..to].to_vec();
            let shared_joint = transport.shared_ablated_joint_anchor[from..to].to_vec();
            let local_joint = transport.local_ablated_joint_anchor[local_from..local_to].to_vec();
            let returned_consequence_sha256 = digest_json(&(
                occurrence.boundary,
                &joint,
                &transport.successor_consequence,
                &occurrence.receiver_boundaries,
            ))?;
            let frontier = frontier_for(&occurrence, &returned_consequence_sha256)?;
            let successor_sha256 = digest_json(&(
                &occurrence.predecessor_continuation_sha256,
                &occurrence.occurrence_sha256,
                &frontier,
                &returned_consequence_sha256,
            ))?;
            let delta = AddressedContinuationDelta {
                predecessor_sha256: occurrence.predecessor_continuation_sha256.clone(),
                successor_sha256: successor_sha256.clone(),
                entering_occurrence_sha256: occurrence.occurrence_sha256.clone(),
                boundary: occurrence.boundary,
                source_incidence_sha256: occurrence.source_incidence_sha256.clone(),
                returned_consequence_sha256,
                frontier,
            };
            validate_delta(&delta)?;
            if let Some(existing) = self.deltas.get(&successor_sha256) {
                if existing != &delta {
                    return Err(NativeMembraneRefusal::ContinuationCollision);
                }
            } else {
                self.deltas.insert(successor_sha256, delta.clone());
            }
            let reconstruction_fibres = occurrence
                .receiver_boundaries
                .iter()
                .map(|boundary| NativeReceiverFibre {
                    boundary: *boundary,
                    members: self
                        .product
                        .boundary_predecessor()
                        .fibres
                        .fibres
                        .iter()
                        .filter(|fibre| fibre.boundary == *boundary)
                        .cloned()
                        .collect(),
                })
                .collect();
            returns.push(NativeInferenceReturn {
                product_identity_sha256: self.product_identity_sha256.clone(),
                continuation: delta,
                consequence: NativePotentialConsequence {
                    boundary: occurrence.boundary,
                    receiver_boundaries: occurrence.receiver_boundaries,
                    joint_anchor: joint,
                    shared_withdrawn_joint_anchor: shared_joint,
                    local_withdrawn_joint_anchor: local_joint,
                    predecessor_consequence: transport.predecessor_consequence.clone(),
                    cultivated_consequence: transport.successor_consequence.clone(),
                    shared_withdrawn_consequence: transport.shared_ablated_consequence.clone(),
                    local_withdrawn_consequence: transport.local_ablated_consequence.clone(),
                    reconstruction_fibres,
                    exact_work: NativeExactWork {
                        entering_cells: self.member_candidate_cells as u64,
                        resident_cells: (transport.families * transport.ports) as u64,
                        returned_cells: (member_anchors
                            + member_anchors * transport.ports
                            + transport.families * transport.ports * (3 + transport.ports))
                            as u64,
                    },
                    apparatus: NativeApparatusReceipt {
                        launches: transport.launches,
                        synchronizations: transport.synchronizations,
                        active_lanes: transport.active_lanes,
                        resident_octets: transport.resident_octets,
                        transfer_octets: transport.host_ingress_octets
                            + transport.host_egress_octets,
                    },
                    open_exterior: self.product.standing().open_exterior.clone(),
                },
            });
        }
        Ok(NativeFrontReturn {
            members: returns,
            interchange: certificate,
        })
    }

    pub fn withdraw_continuation(
        &mut self,
        authorization: AuthorizedContinuationWithdrawal,
    ) -> Result<NativeWithdrawalReturn, NativeMembraneRefusal> {
        let expected = withdrawal_authorization_identity(
            &self.product_identity_sha256,
            &authorization.successor_sha256,
            &authorization.predecessor_sha256,
            &authorization.authorizing_occurrence_sha256,
        );
        if authorization.authorization_sha256 != expected {
            return Err(NativeMembraneRefusal::UnauthorizedWithdrawal);
        }
        let delta = self
            .deltas
            .get(&authorization.successor_sha256)
            .ok_or(NativeMembraneRefusal::UnknownContinuation)?;
        if delta.predecessor_sha256 != authorization.predecessor_sha256
            || self
                .deltas
                .values()
                .any(|other| other.predecessor_sha256 == authorization.successor_sha256)
        {
            return Err(NativeMembraneRefusal::WithdrawalWouldOrphanSuccessor);
        }
        self.deltas.remove(&authorization.successor_sha256);
        Ok(NativeWithdrawalReturn {
            removed_successor_sha256: authorization.successor_sha256,
            restored_predecessor_sha256: authorization.predecessor_sha256,
            exact_local_withdrawal: true,
        })
    }

    fn known_continuations(&self) -> BTreeSet<String> {
        std::iter::once(self.product_identity_sha256.clone())
            .chain(self.deltas.keys().cloned())
            .collect()
    }
}

impl CausalMembrane for NativeInferenceMembrane {
    type Standing = str;
    type Occurrence<'a> = NativeBoundaryOccurrence;
    type Return = NativeInferenceReturn;
    type Error = NativeMembraneRefusal;

    fn standing(&self) -> &Self::Standing {
        &self.product_identity_sha256
    }

    fn receive_occurrence<'a>(
        &mut self,
        occurrence: Self::Occurrence<'a>,
    ) -> Result<Self::Return, Self::Error>
    where
        Self: 'a,
    {
        let mut returned = self.receive_front(vec![occurrence])?;
        returned
            .members
            .pop()
            .ok_or(NativeMembraneRefusal::EmptyFront)
    }
}

pub fn source_incidence_identity(
    occurrence_sha256: &str,
    boundary: BoundaryId,
    candidate_population: &[u32],
) -> String {
    digest_parts(&[
        occurrence_sha256.as_bytes(),
        &boundary.0.to_le_bytes(),
        &candidate_population
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect::<Vec<_>>(),
    ])
}

pub fn withdrawal_authorization_identity(
    product_identity_sha256: &str,
    successor_sha256: &str,
    predecessor_sha256: &str,
    authorizing_occurrence_sha256: &str,
) -> String {
    digest_parts(&[
        product_identity_sha256.as_bytes(),
        successor_sha256.as_bytes(),
        predecessor_sha256.as_bytes(),
        authorizing_occurrence_sha256.as_bytes(),
    ])
}

fn validate_occurrence(
    occurrence: &NativeBoundaryOccurrence,
    member_candidate_cells: usize,
    admitted: &BTreeSet<BoundaryId>,
    known: &BTreeSet<String>,
) -> Result<(), NativeMembraneRefusal> {
    if !valid_digest(&occurrence.occurrence_sha256)
        || !valid_digest(&occurrence.predecessor_continuation_sha256)
        || !valid_digest(&occurrence.source_incidence_sha256)
        || !valid_digest(&occurrence.lineage_sha256)
        || !known.contains(&occurrence.predecessor_continuation_sha256)
    {
        return Err(NativeMembraneRefusal::UnknownContinuation);
    }
    if !admitted.contains(&occurrence.boundary)
        || occurrence.receiver_boundaries.is_empty()
        || occurrence
            .receiver_boundaries
            .iter()
            .any(|boundary| !admitted.contains(boundary))
    {
        return Err(NativeMembraneRefusal::Boundary);
    }
    if occurrence.candidate_population.len() != member_candidate_cells
        || occurrence.candidate_population.contains(&0)
    {
        return Err(NativeMembraneRefusal::IncidenceShape);
    }
    if occurrence.source_incidence_sha256
        != source_incidence_identity(
            &occurrence.occurrence_sha256,
            occurrence.boundary,
            &occurrence.candidate_population,
        )
    {
        return Err(NativeMembraneRefusal::IncidenceIdentity);
    }
    if occurrence.frontier_aperture < 3 {
        return Err(NativeMembraneRefusal::FrontierAperture);
    }
    Ok(())
}

fn frontier_for(
    occurrence: &NativeBoundaryOccurrence,
    returned_consequence_sha256: &str,
) -> Result<Vec<NativeFrontierOccurrence>, NativeMembraneRefusal> {
    let incidences = [
        occurrence.source_incidence_sha256.clone(),
        digest_parts(&[
            occurrence.source_incidence_sha256.as_bytes(),
            occurrence.lineage_sha256.as_bytes(),
        ]),
        digest_parts(&[
            occurrence.lineage_sha256.as_bytes(),
            returned_consequence_sha256.as_bytes(),
        ]),
    ];
    let consequences = [
        digest_parts(&[
            occurrence.occurrence_sha256.as_bytes(),
            occurrence.source_incidence_sha256.as_bytes(),
        ]),
        returned_consequence_sha256.to_owned(),
        digest_parts(&[
            returned_consequence_sha256.as_bytes(),
            occurrence.predecessor_continuation_sha256.as_bytes(),
        ]),
    ];
    let mut predecessor = occurrence.predecessor_continuation_sha256.clone();
    let mut frontier = Vec::with_capacity(3);
    for ordinal in 0..3u32 {
        let address = digest_json(&(
            &predecessor,
            &incidences[ordinal as usize],
            &consequences[ordinal as usize],
            ordinal,
        ))?;
        frontier.push(NativeFrontierOccurrence {
            ordinal,
            predecessor_sha256: predecessor,
            incidence_sha256: incidences[ordinal as usize].clone(),
            consequence_sha256: consequences[ordinal as usize].clone(),
            address_sha256: address.clone(),
        });
        predecessor = address;
    }
    Ok(frontier)
}

fn front_certificate(
    occurrences: &[NativeBoundaryOccurrence],
    member_candidate_cells: usize,
) -> Result<FrontCertificate, NativeMembraneRefusal> {
    let members = occurrences.len() as u64;
    let input_extent = members
        .checked_mul(member_candidate_cells as u64)
        .ok_or(NativeMembraneRefusal::FootprintOverflow)?;
    let shared_read_from = input_extent;
    let shared_read_to = shared_read_from
        .checked_add(1)
        .ok_or(NativeMembraneRefusal::FootprintOverflow)?;
    let output_from = shared_read_to;
    let output_span = 3u64;
    let mut footprints = Vec::with_capacity(occurrences.len());
    for member in 0..members {
        let read_from = member
            .checked_mul(member_candidate_cells as u64)
            .ok_or(NativeMembraneRefusal::FootprintOverflow)?;
        let read_to = read_from
            .checked_add(member_candidate_cells as u64)
            .ok_or(NativeMembraneRefusal::FootprintOverflow)?;
        let write_from = output_from
            .checked_add(
                member
                    .checked_mul(output_span)
                    .ok_or(NativeMembraneRefusal::FootprintOverflow)?,
            )
            .ok_or(NativeMembraneRefusal::FootprintOverflow)?;
        footprints.push(MemberFootprint {
            reads: vec![(read_from, read_to), (shared_read_from, shared_read_to)],
            writes: vec![(write_from, write_from + output_span)],
        });
    }
    Ok(certify_footprints(&footprints))
}

fn ordered_deltas(
    root: &str,
    deltas: &BTreeMap<String, AddressedContinuationDelta>,
) -> Result<Vec<AddressedContinuationDelta>, NativeMembraneRefusal> {
    let mut known = BTreeSet::from([root.to_owned()]);
    let mut remaining = deltas.values().cloned().collect::<Vec<_>>();
    let mut ordered = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        let Some(at) = remaining
            .iter()
            .position(|delta| known.contains(&delta.predecessor_sha256))
        else {
            return Err(NativeMembraneRefusal::RestLineage);
        };
        let delta = remaining.remove(at);
        known.insert(delta.successor_sha256.clone());
        ordered.push(delta);
    }
    Ok(ordered)
}

fn validate_delta(delta: &AddressedContinuationDelta) -> Result<(), NativeMembraneRefusal> {
    if !valid_digest(&delta.predecessor_sha256)
        || !valid_digest(&delta.successor_sha256)
        || !valid_digest(&delta.entering_occurrence_sha256)
        || !valid_digest(&delta.source_incidence_sha256)
        || !valid_digest(&delta.returned_consequence_sha256)
        || delta.frontier.len() != 3
        || delta
            .frontier
            .iter()
            .any(|front| !valid_digest(&front.address_sha256))
    {
        return Err(NativeMembraneRefusal::RestLineage);
    }
    Ok(())
}

fn digest_json(value: &impl Serialize) -> Result<String, NativeMembraneRefusal> {
    serde_json::to_vec(value)
        .map(|bytes| digest_parts(&[&bytes]))
        .map_err(|error| NativeMembraneRefusal::Rest(error.to_string()))
}

fn digest_parts(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    format!("{:x}", digest.finalize())
}

fn valid_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum NativeMembraneRefusal {
    #[error("the native request front is empty")]
    EmptyFront,
    #[error("the addressed continuation is absent from this product")]
    UnknownContinuation,
    #[error("the nominal boundary or receiver aperture is absent")]
    Boundary,
    #[error("the entering incidence population does not fit the mounted organ")]
    IncidenceShape,
    #[error("the entering incidence identity does not bind its population")]
    IncidenceIdentity,
    #[error("the requested frontier aperture cannot return ingress, conduct and return")]
    FrontierAperture,
    #[error("the request-front apparatus footprint overflowed")]
    FootprintOverflow,
    #[error("the co-present request front did not certify interchange")]
    Interchange,
    #[error("the continuation identity collided with different local material")]
    ContinuationCollision,
    #[error("the continuation withdrawal was not explicitly authorized")]
    UnauthorizedWithdrawal,
    #[error("the requested continuation withdrawal would orphan a successor")]
    WithdrawalWouldOrphanSuccessor,
    #[error("the native standing identity moved")]
    RestIdentity,
    #[error("the native standing lineage is not reconstructible")]
    RestLineage,
    #[error("the cultivated product refused: {0}")]
    Cultivation(BoundaryCultivationRefusal),
    #[error("the resident apparatus refused: {0}")]
    Apparatus(String),
    #[error("the native rest refused: {0}")]
    Rest(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mark(value: u8) -> String {
        format!("{value:064x}")
    }

    #[test]
    fn incidence_binds_occurrence_boundary_and_population() {
        let a = source_incidence_identity(&mark(1), BoundaryId(7), &[1, 2, 3]);
        let b = source_incidence_identity(&mark(1), BoundaryId(8), &[1, 2, 3]);
        let c = source_incidence_identity(&mark(1), BoundaryId(7), &[1, 2, 4]);
        assert_ne!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn withdrawal_authorization_binds_the_exact_local_edge() {
        let a = withdrawal_authorization_identity(&mark(1), &mark(2), &mark(3), &mark(4));
        let b = withdrawal_authorization_identity(&mark(1), &mark(2), &mark(5), &mark(4));
        assert_ne!(a, b);
    }
}
