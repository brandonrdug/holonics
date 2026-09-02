//! Exact constituted diffusion through the live circulation boundary.
//!
//! Native incidence founds the diffusion complex. Capacities, conductances, interval, source, and
//! receiver boundary are declared exact physical/apparatus coordinates. No codec surface, cached
//! semantic history, model label, or generated output participates in the law.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    diffusion::{
        DiffusionBranch, DiffusionComplex, DiffusionEvent, DiffusionNode, DiffusionReceipt,
        DiffusionStanding, ExactDiffusionLaw,
    },
    native_spool::NativeTransportScaffold,
    receiver_exact_compression::ReceiverId,
    receiver_history_compression::NativeStateId,
    CurrentBranchId, CurrentNodeId, EventId,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{Signed, Zero};
use serde::{Deserialize, Serialize};

use super::{
    InferenceConfigurationAddress, NativeCirculationBoundary, NativeCirculationSession,
    NativeOwnedOpenObligation, NativeOwnedOpenScope, NativeSessionError,
};

pub const NATIVE_DIFFUSIVE_CIRCULATION_SCHEMA: &str = "soma-life.native-diffusive-circulation.v1";

/// Exact native realization of one finite diffusion law.
#[derive(Debug)]
pub struct NativeDiffusionLaw {
    pub schema: String,
    pub spool_address: String,
    native_to_node: BTreeMap<NativeStateId, CurrentNodeId>,
    node_to_native: BTreeMap<CurrentNodeId, NativeStateId>,
    branch_to_occurrence: BTreeMap<CurrentBranchId, EventId>,
    boundary: BTreeSet<NativeStateId>,
    law: ExactDiffusionLaw,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeDiffusionStanding {
    pub content: BTreeMap<NativeStateId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeDiffusionIngress {
    pub occurrence: EventId,
    pub interval: Rat,
    pub source: BTreeMap<NativeStateId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeDiffusionEmission {
    pub occurrence: EventId,
    pub receiver: ReceiverId,
    pub boundary_content: BTreeMap<NativeStateId, Rat>,
    pub boundary_potential: BTreeMap<NativeStateId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeDiffusiveBoundary {
    pub schema: String,
    pub generation: u64,
    pub configuration: InferenceConfigurationAddress,
    pub spool_address: String,
    pub ingress: NativeDiffusionIngress,
    pub standing_before: NativeDiffusionStanding,
    pub standing_after: NativeDiffusionStanding,
    pub emission: NativeDiffusionEmission,
    pub native_to_node: BTreeMap<NativeStateId, CurrentNodeId>,
    pub branch_to_occurrence: BTreeMap<CurrentBranchId, EventId>,
    pub receipt: DiffusionReceipt,
    pub open_obligations: Vec<NativeOwnedOpenObligation>,
}

/// The common runtime boundary family. Both members are fixed-morphology conduct; only a later
/// returned interaction may cultivate the package.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "transport", rename_all = "kebab-case")]
pub enum NativeCirculationEvent {
    AddressedSuccessor(NativeCirculationBoundary),
    ConstitutedDiffusion(NativeDiffusiveBoundary),
}

impl NativeDiffusionLaw {
    pub fn found(
        morphology: &NativeTransportScaffold,
        spool_address: &str,
        capacities: BTreeMap<NativeStateId, Rat>,
        conductances: BTreeMap<EventId, Rat>,
        boundary: BTreeSet<NativeStateId>,
    ) -> Result<Self, NativeSessionError> {
        morphology
            .validate()
            .map_err(|error| NativeSessionError::Conduct(error.to_string()))?;
        let spool = morphology
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSessionError::Conduct("unknown diffusion spool".to_owned()))?;
        if capacities.keys().copied().collect::<BTreeSet<_>>() != spool.native_population
            || capacities.values().any(|capacity| !capacity.is_positive())
            || boundary.is_empty()
            || !boundary.is_subset(&spool.native_population)
        {
            return Err(NativeSessionError::Conduct(
                "diffusion capacity or boundary does not cover the native population".to_owned(),
            ));
        }
        let incidence = spool
            .threads
            .iter()
            .flat_map(|thread| &thread.incidence)
            .collect::<Vec<_>>();
        let incidence_occurrences = incidence
            .iter()
            .map(|term| term.occurrence)
            .collect::<BTreeSet<_>>();
        if incidence.is_empty()
            || incidence_occurrences.len() != incidence.len()
            || conductances.keys().copied().collect::<BTreeSet<_>>() != incidence_occurrences
            || conductances.values().any(Signed::is_negative)
        {
            return Err(NativeSessionError::Conduct(
                "diffusion conductance does not match native incidence".to_owned(),
            ));
        }

        let native_to_node = spool
            .native_population
            .iter()
            .map(|native| (*native, CurrentNodeId(native.0)))
            .collect::<BTreeMap<_, _>>();
        let node_to_native = native_to_node
            .iter()
            .map(|(native, node)| (*node, *native))
            .collect::<BTreeMap<_, _>>();
        let nodes = capacities.iter().map(|(native, capacity)| DiffusionNode {
            node: native_to_node[native],
            capacity: capacity.clone(),
        });
        let mut branch_to_occurrence = BTreeMap::new();
        let branches = incidence
            .iter()
            .map(|term| {
                let branch = CurrentBranchId(term.occurrence.0);
                if branch_to_occurrence
                    .insert(branch, term.occurrence)
                    .is_some()
                {
                    return Err(NativeSessionError::Conduct(
                        "native occurrence does not uniquely address a diffusion branch".to_owned(),
                    ));
                }
                let coefficient = Rat::from_integer(BigInt::from(term.coefficient.unsigned_abs()));
                let conductance = &conductances[&term.occurrence] * coefficient;
                let (source, target) = if term.coefficient.is_negative() {
                    (term.to, term.from)
                } else {
                    (term.from, term.to)
                };
                Ok(DiffusionBranch {
                    branch,
                    source: native_to_node[&source],
                    target: native_to_node[&target],
                    conductance,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let complex = DiffusionComplex::new(nodes, branches)
            .map_err(|error| NativeSessionError::Conduct(error.to_string()))?;
        let law = ExactDiffusionLaw::with_boundary(
            complex,
            boundary.iter().map(|native| native_to_node[native]),
        )
        .map_err(|error| NativeSessionError::Conduct(error.to_string()))?;
        Ok(Self {
            schema: NATIVE_DIFFUSIVE_CIRCULATION_SCHEMA.to_owned(),
            spool_address: spool_address.to_owned(),
            native_to_node,
            node_to_native,
            branch_to_occurrence,
            boundary,
            law,
        })
    }

    pub fn initial_standing(
        &self,
        content: BTreeMap<NativeStateId, Rat>,
    ) -> Result<NativeDiffusionStanding, NativeSessionError> {
        let standing = NativeDiffusionStanding { content };
        let _ = self.engine_standing(&standing)?;
        Ok(standing)
    }

    pub fn transfer_factorizations(&self) -> usize {
        self.law.transfer_cache_entries()
    }

    fn engine_standing(
        &self,
        standing: &NativeDiffusionStanding,
    ) -> Result<DiffusionStanding, NativeSessionError> {
        if standing.content.keys().copied().collect::<BTreeSet<_>>()
            != self.native_to_node.keys().copied().collect()
        {
            return Err(NativeSessionError::Conduct(
                "diffusion standing does not cover the native population".to_owned(),
            ));
        }
        self.law
            .initial_standing(
                standing
                    .content
                    .iter()
                    .map(|(native, content)| (self.native_to_node[native], content.clone()))
                    .collect(),
            )
            .map_err(|error| NativeSessionError::Conduct(error.to_string()))
    }

    fn native_content(&self, standing: &DiffusionStanding) -> BTreeMap<NativeStateId, Rat> {
        standing
            .content
            .iter()
            .map(|(node, content)| (self.node_to_native[node], content.clone()))
            .collect()
    }
}

impl NativeCirculationSession {
    pub fn conduct_event(
        &self,
        request: holonic_engine::native_ecology::holonic_intelligence::NativeInferenceRequest,
    ) -> Result<NativeCirculationEvent, NativeSessionError> {
        self.conduct(request)
            .map(NativeCirculationEvent::AddressedSuccessor)
    }

    pub fn diffuse(
        &self,
        law: &NativeDiffusionLaw,
        standing: &NativeDiffusionStanding,
        ingress: NativeDiffusionIngress,
    ) -> Result<NativeCirculationEvent, NativeSessionError> {
        if law.schema != NATIVE_DIFFUSIVE_CIRCULATION_SCHEMA
            || ingress.interval <= Rat::zero()
            || ingress
                .source
                .keys()
                .any(|native| !law.native_to_node.contains_key(native))
        {
            return Err(NativeSessionError::Conduct(
                "malformed native diffusion ingress".to_owned(),
            ));
        }
        let standing_before = law.engine_standing(standing)?;
        let event = DiffusionEvent {
            interval: ingress.interval.clone(),
            source: ingress
                .source
                .iter()
                .map(|(native, source)| (law.native_to_node[native], source.clone()))
                .collect(),
        };
        let (standing_after, receipt) = law
            .law
            .enact(&standing_before, &event)
            .map_err(|error| NativeSessionError::Conduct(error.to_string()))?;
        if !receipt.conservation_residual.is_zero()
            || receipt
                .balances
                .iter()
                .any(|balance| !balance.exact_residual.is_zero())
        {
            return Err(NativeSessionError::Conduct(
                "exact diffusion returned a nonzero balance residual".to_owned(),
            ));
        }
        let after = NativeDiffusionStanding {
            content: law.native_content(&standing_after),
        };
        let boundary_content = law
            .boundary
            .iter()
            .map(|native| (*native, after.content[native].clone()))
            .collect();
        let boundary_potential = law
            .boundary
            .iter()
            .map(|native| {
                (
                    *native,
                    receipt.potential_after[&law.native_to_node[native]].clone(),
                )
            })
            .collect();
        let spool = self
            .package
            .hot()
            .native()
            .spools
            .iter()
            .find(|spool| spool.address == law.spool_address)
            .ok_or_else(|| NativeSessionError::Conduct("diffusion spool departed".to_owned()))?;
        let mut open_obligations = spool
            .open_exterior
            .iter()
            .map(|testimony| NativeOwnedOpenObligation {
                scope: NativeOwnedOpenScope::Spool,
                testimony: testimony.clone(),
            })
            .collect::<Vec<_>>();
        open_obligations.extend(self.package.hot().native().open_exterior.iter().map(
            |testimony| NativeOwnedOpenObligation {
                scope: NativeOwnedOpenScope::Scaffold,
                testimony: testimony.clone(),
            },
        ));
        Ok(NativeCirculationEvent::ConstitutedDiffusion(
            NativeDiffusiveBoundary {
                schema: NATIVE_DIFFUSIVE_CIRCULATION_SCHEMA.to_owned(),
                generation: self.generation(),
                configuration: self.configuration.at(ingress.occurrence),
                spool_address: law.spool_address.clone(),
                emission: NativeDiffusionEmission {
                    occurrence: ingress.occurrence,
                    receiver: self.configuration.address.receiver,
                    boundary_content,
                    boundary_potential,
                },
                ingress,
                standing_before: standing.clone(),
                standing_after: after,
                native_to_node: law.native_to_node.clone(),
                branch_to_occurrence: law.branch_to_occurrence.clone(),
                receipt,
                open_obligations,
            },
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
            NativeInferenceAddress, NativeInferenceRequest,
        },
        receiver_exact_compression::ReceiverId,
        soulkiller::dismantle,
        BoundaryId,
    };
    use num_traits::One;

    use crate::native_intelligence::{
        consume_dismantling_return, MorphologyLineage, NativeCirculationConfiguration,
        NativeMorphologyPackage,
    };

    fn session() -> NativeCirculationSession {
        let excitation = ForeignBf16Excitation {
            event: EventId(1),
            predecessor: None,
            entering_boundary: BoundaryId(1),
            emitting_boundary: BoundaryId(2),
            source_occurrence: "cold/1".to_owned(),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![0x3f80],
            returned_codewords: vec![0x4000],
            interventions: BTreeSet::from(["withdraw/1".to_owned()]),
            receiver_consequences: BTreeSet::from(["return/1".to_owned()]),
        };
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![excitation],
        })
        .expect("dismantle");
        let (hot, _) = consume_dismantling_return(returned).expect("hot");
        let package = NativeMorphologyPackage::found(
            hot,
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        NativeCirculationSession::mount(
            package,
            NativeCirculationConfiguration::found(InferenceConfigurationAddress {
                ingress_aperture: "native-addressed-occurrence".to_owned(),
                occurrence: EventId(1),
                receiver: ReceiverId(7),
                continuation_receiver: "exterior-receiver-decision".to_owned(),
                world_return_law: "genuinely-later-return".to_owned(),
                emission_codec: "owned-structural-boundary".to_owned(),
                apparatus: "exact-diffusion".to_owned(),
                stochastic_current: None,
            })
            .expect("configuration"),
        )
        .expect("session")
    }

    #[test]
    fn addressed_and_diffusive_conduct_share_one_event_family() {
        let session = session();
        let native = session.package().hot().native();
        let spool = &native.spools[0];
        let capacities = spool
            .native_population
            .iter()
            .map(|native| (*native, Rat::one()))
            .collect();
        let conductances = spool
            .threads
            .iter()
            .flat_map(|thread| &thread.incidence)
            .map(|term| (term.occurrence, Rat::one()))
            .collect();
        let boundary = spool.native_population.iter().copied().collect();
        let law =
            NativeDiffusionLaw::found(native, &spool.address, capacities, conductances, boundary)
                .expect("diffusion law");
        let first_native = *spool.native_population.iter().next().expect("native state");
        let standing = law
            .initial_standing(
                spool
                    .native_population
                    .iter()
                    .map(|native| {
                        (
                            *native,
                            if *native == first_native {
                                Rat::one()
                            } else {
                                Rat::zero()
                            },
                        )
                    })
                    .collect(),
            )
            .expect("standing");
        let diffusive = session
            .diffuse(
                &law,
                &standing,
                NativeDiffusionIngress {
                    occurrence: EventId(10),
                    interval: Rat::one(),
                    source: BTreeMap::new(),
                },
            )
            .expect("diffusive event");
        let NativeCirculationEvent::ConstitutedDiffusion(first) = diffusive else {
            panic!("diffusive event species");
        };
        assert!(first.receipt.conservation_residual.is_zero());
        assert!(first
            .receipt
            .balances
            .iter()
            .all(|balance| balance.exact_residual.is_zero()));
        assert!(!first.receipt.transfer.reused_factorization);
        assert_eq!(law.transfer_factorizations(), 1);

        let NativeCirculationEvent::ConstitutedDiffusion(second) = session
            .diffuse(
                &law,
                &standing,
                NativeDiffusionIngress {
                    occurrence: EventId(11),
                    interval: Rat::one(),
                    source: BTreeMap::new(),
                },
            )
            .expect("second diffusive event")
        else {
            panic!("second diffusive event species");
        };
        assert!(second.receipt.transfer.reused_factorization);

        let request = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: spool.address.clone(),
                thread: spool.threads[0].address.clone(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(7),
        };
        assert!(matches!(
            session.conduct_event(request).expect("addressed event"),
            NativeCirculationEvent::AddressedSuccessor(_)
        ));
    }

    #[test]
    fn incomplete_capacity_and_surface_free_ingress_refuse_or_leave_law_fixed() {
        let session = session();
        let native = session.package().hot().native();
        let spool = &native.spools[0];
        assert!(NativeDiffusionLaw::found(
            native,
            &spool.address,
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeSet::new(),
        )
        .is_err());
    }
}
