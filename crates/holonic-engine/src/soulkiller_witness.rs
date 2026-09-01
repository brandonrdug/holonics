//! Exterior testimony for dismantling one inherited realization into native spools.
//!
//! This module is deliberately outside [`crate::native_spool`].  It owns realization names,
//! artifact identities, executor testimony, implementation coordinates, interventions, and the
//! reconstruction relation from exterior fragments to native threads.  Native spools contain none
//! of these fields and carry no callable edge back to this witness.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    native_spool::{NativeSpoolRefusal, NativeTransportScaffold},
    receiver_exact_compression::{InputId, ReceiverId},
};

pub const EXTERIOR_SOULKILLER_WITNESS_SCHEMA: &str =
    "holonic-engine.exterior-soulkiller-witness.v2";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorArtifactIdentity {
    pub sha256: String,
    pub octets: u64,
}

impl ExteriorArtifactIdentity {
    pub fn measure(bytes: &[u8]) -> Self {
        Self {
            sha256: hex(&Sha256::digest(bytes)),
            octets: bytes.len() as u64,
        }
    }

    fn validate(&self) -> bool {
        self.octets > 0 && valid_sha256(&self.sha256)
    }
}

/// Cold identity and implementation chart of the admitted inherited realization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForeignRealizationTestimony {
    pub name: String,
    pub format: String,
    pub artifact: ExteriorArtifactIdentity,
    pub topology: Vec<String>,
    pub coordinate_roles: Vec<String>,
}

/// Apparatus testimony for the bounded excitation/dissection session.  This is not an executor
/// handle and cannot conduct another occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForeignExecutionTestimony {
    pub runtime: String,
    pub device: String,
    pub apparatus: ExteriorArtifactIdentity,
    pub admitted_receiver_family: BTreeSet<ReceiverId>,
    pub session_closed: bool,
}

/// One exterior fragment and the source chart in which the dissection addressed it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForeignFragmentTestimony {
    pub address: String,
    pub coordinates: BTreeMap<String, String>,
    pub interventions: BTreeSet<String>,
}

/// The exterior side of one extraction map.  Multiple fragments may found one native thread, but
/// the native thread address is the only value crossing toward the neutral scaffold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ThreadExtractionWitness {
    pub native_thread: String,
    pub founding_fragments: BTreeSet<String>,
    pub checked_generator_word: Vec<InputId>,
    pub receiver_family: BTreeSet<ReceiverId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForeignShortestSeparator {
    pub left_fragment: String,
    pub right_fragment: String,
    pub receiver: ReceiverId,
    pub word: Vec<InputId>,
}

/// Complete exterior condensation testimony for one native spool.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SpoolCondensationWitness {
    pub native_spool: String,
    pub native_threads: BTreeSet<String>,
    pub founding_fragments: BTreeSet<String>,
    pub collapsed_fragment_fibres: Vec<BTreeSet<String>>,
    pub shortest_separators: Vec<ForeignShortestSeparator>,
}

/// Physically exterior ancestry and reconstruction testimony.
///
/// The witness binds to the canonical native scaffold bytes in one direction. The scaffold
/// carries no reciprocal witness identity and therefore remains independently mountable.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorSoulkillerWitness {
    pub schema: String,
    pub realization: ForeignRealizationTestimony,
    pub execution: ForeignExecutionTestimony,
    pub fragments: Vec<ForeignFragmentTestimony>,
    pub thread_extractions: Vec<ThreadExtractionWitness>,
    pub spool_condensations: Vec<SpoolCondensationWitness>,
    pub native_scaffold_sha256: String,
    pub reconstruction_fibre: BTreeSet<String>,
    pub unexcited_capability: BTreeSet<String>,
    pub open_exterior: Vec<String>,
}

impl ExteriorSoulkillerWitness {
    #[allow(clippy::too_many_arguments)]
    pub fn seal(
        scaffold: &NativeTransportScaffold,
        realization: ForeignRealizationTestimony,
        execution: ForeignExecutionTestimony,
        fragments: Vec<ForeignFragmentTestimony>,
        thread_extractions: Vec<ThreadExtractionWitness>,
        spool_condensations: Vec<SpoolCondensationWitness>,
        reconstruction_fibre: BTreeSet<String>,
        unexcited_capability: BTreeSet<String>,
        open_exterior: Vec<String>,
    ) -> Result<Self, ExteriorSoulkillerWitnessRefusal> {
        let native_scaffold_sha256 = scaffold_identity(scaffold)?;
        let witness = Self {
            schema: EXTERIOR_SOULKILLER_WITNESS_SCHEMA.to_owned(),
            realization,
            execution,
            fragments,
            thread_extractions,
            spool_condensations,
            native_scaffold_sha256,
            reconstruction_fibre,
            unexcited_capability,
            open_exterior,
        };
        witness.validate(scaffold)?;
        Ok(witness)
    }

    pub fn read(
        bytes: &[u8],
        scaffold: &NativeTransportScaffold,
    ) -> Result<Self, ExteriorSoulkillerWitnessRefusal> {
        let witness: Self = serde_json::from_slice(bytes)
            .map_err(|error| ExteriorSoulkillerWitnessRefusal::Wire(error.to_string()))?;
        witness.validate(scaffold)?;
        Ok(witness)
    }

    pub fn canonical_bytes(
        &self,
        scaffold: &NativeTransportScaffold,
    ) -> Result<Vec<u8>, ExteriorSoulkillerWitnessRefusal> {
        self.validate(scaffold)?;
        serde_json::to_vec(self)
            .map_err(|error| ExteriorSoulkillerWitnessRefusal::Wire(error.to_string()))
    }

    pub fn validate(
        &self,
        scaffold: &NativeTransportScaffold,
    ) -> Result<(), ExteriorSoulkillerWitnessRefusal> {
        if self.schema != EXTERIOR_SOULKILLER_WITNESS_SCHEMA {
            return Err(ExteriorSoulkillerWitnessRefusal::Schema(
                self.schema.clone(),
            ));
        }
        scaffold
            .validate()
            .map_err(ExteriorSoulkillerWitnessRefusal::NativeScaffold)?;
        if scaffold_identity(scaffold)? != self.native_scaffold_sha256 {
            return Err(ExteriorSoulkillerWitnessRefusal::NativeScaffoldIdentity);
        }
        if self.realization.name.is_empty()
            || self.realization.format.is_empty()
            || !self.realization.artifact.validate()
            || self.realization.topology.is_empty()
            || self.realization.coordinate_roles.is_empty()
            || self.realization.topology.iter().any(String::is_empty)
            || self
                .realization
                .coordinate_roles
                .iter()
                .any(String::is_empty)
        {
            return Err(ExteriorSoulkillerWitnessRefusal::Realization);
        }
        if self.execution.runtime.is_empty()
            || self.execution.device.is_empty()
            || !self.execution.apparatus.validate()
            || self.execution.admitted_receiver_family.is_empty()
            || !self.execution.session_closed
        {
            return Err(ExteriorSoulkillerWitnessRefusal::Execution);
        }

        let mut fragments = BTreeMap::new();
        for fragment in &self.fragments {
            if fragment.address.is_empty()
                || fragment.coordinates.is_empty()
                || fragment.coordinates.keys().any(String::is_empty)
                || fragment.coordinates.values().any(String::is_empty)
                || fragment.interventions.iter().any(String::is_empty)
                || fragments
                    .insert(fragment.address.as_str(), fragment)
                    .is_some()
            {
                return Err(ExteriorSoulkillerWitnessRefusal::Fragment);
            }
        }
        if fragments.is_empty() {
            return Err(ExteriorSoulkillerWitnessRefusal::Fragment);
        }

        let native_threads = scaffold
            .spools
            .iter()
            .flat_map(|spool| spool.threads.iter().map(|thread| thread.address.as_str()))
            .collect::<BTreeSet<_>>();
        let native_spools = scaffold
            .spools
            .iter()
            .map(|spool| spool.address.as_str())
            .collect::<BTreeSet<_>>();
        let mut extracted_threads = BTreeSet::new();
        let mut fragments_by_thread = BTreeMap::<&str, BTreeSet<&str>>::new();
        for extraction in &self.thread_extractions {
            if !native_threads.contains(extraction.native_thread.as_str())
                || !extracted_threads.insert(extraction.native_thread.as_str())
                || extraction.founding_fragments.is_empty()
                || extraction.checked_generator_word.is_empty()
                || extraction.receiver_family.is_empty()
                || extraction
                    .founding_fragments
                    .iter()
                    .any(|fragment| !fragments.contains_key(fragment.as_str()))
            {
                return Err(ExteriorSoulkillerWitnessRefusal::ThreadExtraction);
            }
            fragments_by_thread.insert(
                extraction.native_thread.as_str(),
                extraction
                    .founding_fragments
                    .iter()
                    .map(String::as_str)
                    .collect(),
            );
        }
        if extracted_threads != native_threads {
            return Err(ExteriorSoulkillerWitnessRefusal::ThreadExtraction);
        }

        let mut condensed_spools = BTreeSet::new();
        for condensation in &self.spool_condensations {
            let Some(spool) = scaffold
                .spools
                .iter()
                .find(|spool| spool.address == condensation.native_spool)
            else {
                return Err(ExteriorSoulkillerWitnessRefusal::SpoolCondensation);
            };
            let expected_threads = spool
                .threads
                .iter()
                .map(|thread| thread.address.as_str())
                .collect::<BTreeSet<_>>();
            let expected_fragments = expected_threads
                .iter()
                .flat_map(|thread| fragments_by_thread[thread].iter().copied())
                .collect::<BTreeSet<_>>();
            if !native_spools.contains(condensation.native_spool.as_str())
                || !condensed_spools.insert(condensation.native_spool.as_str())
                || condensation
                    .native_threads
                    .iter()
                    .map(String::as_str)
                    .collect::<BTreeSet<_>>()
                    != expected_threads
                || condensation
                    .founding_fragments
                    .iter()
                    .map(String::as_str)
                    .collect::<BTreeSet<_>>()
                    != expected_fragments
            {
                return Err(ExteriorSoulkillerWitnessRefusal::SpoolCondensation);
            }
            let mut collapsed_members = BTreeSet::new();
            for fibre in &condensation.collapsed_fragment_fibres {
                if fibre.len() < 2
                    || fibre
                        .iter()
                        .any(|fragment| !condensation.founding_fragments.contains(fragment))
                    || fibre
                        .iter()
                        .any(|fragment| !collapsed_members.insert(fragment.as_str()))
                {
                    return Err(ExteriorSoulkillerWitnessRefusal::SpoolCondensation);
                }
            }
            for separator in &condensation.shortest_separators {
                if separator.left_fragment == separator.right_fragment
                    || separator.word.is_empty()
                    || !condensation
                        .founding_fragments
                        .contains(&separator.left_fragment)
                    || !condensation
                        .founding_fragments
                        .contains(&separator.right_fragment)
                {
                    return Err(ExteriorSoulkillerWitnessRefusal::SpoolCondensation);
                }
            }
        }
        if condensed_spools != native_spools {
            return Err(ExteriorSoulkillerWitnessRefusal::SpoolCondensation);
        }

        let fragment_addresses = fragments.keys().copied().collect::<BTreeSet<_>>();
        let retained_addresses = self
            .reconstruction_fibre
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        if !fragment_addresses.is_subset(&retained_addresses)
            || self.unexcited_capability.iter().any(String::is_empty)
            || !self
                .unexcited_capability
                .iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>()
                .is_subset(&retained_addresses)
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(ExteriorSoulkillerWitnessRefusal::ReconstructionFibre);
        }
        Ok(())
    }
}

fn scaffold_identity(
    scaffold: &NativeTransportScaffold,
) -> Result<String, ExteriorSoulkillerWitnessRefusal> {
    let bytes = scaffold
        .canonical_bytes()
        .map_err(ExteriorSoulkillerWitnessRefusal::NativeScaffold)?;
    Ok(hex(&Sha256::digest(bytes)))
}

fn valid_sha256(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[derive(Debug, Error)]
pub enum ExteriorSoulkillerWitnessRefusal {
    #[error("exterior Soulkiller witness wire refused: {0}")]
    Wire(String),
    #[error("unknown exterior Soulkiller witness schema {0}")]
    Schema(String),
    #[error("native transport scaffold refused: {0}")]
    NativeScaffold(#[source] NativeSpoolRefusal),
    #[error("the exterior witness does not bind the supplied native scaffold")]
    NativeScaffoldIdentity,
    #[error("foreign realization testimony is empty or malformed")]
    Realization,
    #[error("foreign execution testimony is empty, malformed, or still live")]
    Execution,
    #[error("foreign fragment testimony is empty, repeated, or malformed")]
    Fragment,
    #[error("the exterior thread extraction does not cover the native scaffold exactly")]
    ThreadExtraction,
    #[error("the exterior spool condensation does not cover the native scaffold exactly")]
    SpoolCondensation,
    #[error("the exterior reconstruction fibre is incomplete or malformed")]
    ReconstructionFibre,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort,
        native_spool::{
            NATIVE_SPOOL_SCHEMA, NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
            NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent,
            NativeGeneratorStep, NativeIncidenceTerm, NativeParametronCell,
            NativeReceiverConsequence, NativeSpool, NativeThread, NativeThreadHand,
            NativeThreadOccurrence, NativeTransportScaffold,
        },
        receiver_exact_compression::Observation,
        receiver_history_compression::{NativeStateId, ReceiverFactor},
    };

    fn scaffold() -> NativeTransportScaffold {
        let event = EventId(1);
        let native = NativeStateId(0);
        let receiver = ReceiverId(2);
        let generator = InputId(3);
        let one = ExactComplexWaveCurrent::one();
        let thread = NativeThread {
            schema: NATIVE_THREAD_SCHEMA.to_owned(),
            address: "thread/native-loop".to_owned(),
            entering_boundary: BoundaryId(4),
            emitting_boundary: BoundaryId(4),
            entering_carrier: "native-current".to_owned(),
            emitting_carrier: "native-current".to_owned(),
            occurrences: vec![NativeThreadOccurrence {
                occurrence: event,
                predecessor: None,
                entering_port: OccurrencePort::input(event, 0),
                emitting_port: OccurrencePort::output(event, 0),
                entering_native: native,
                emitting_native: native,
            }],
            native_support: BTreeSet::from([native]),
            incidence: vec![NativeIncidenceTerm {
                occurrence: event,
                from: native,
                to: native,
                coefficient: 1,
            }],
            parametrons: vec![NativeParametronCell {
                native,
                section: one.clone(),
                current: one.clone(),
                relative_phase: ExactUnitConicPhase::identity(),
                hand: NativeThreadHand::Along,
            }],
            constitutive_responses: vec![NativeConstitutiveResponse {
                native,
                receiver,
                presented: one.clone(),
                stored: one,
            }],
            chronology: vec![generator],
            receiver_consequences: vec![NativeReceiverConsequence {
                native,
                receiver,
                observation: Observation(5),
            }],
            obstruction: None,
            open_exterior: Vec::new(),
            reconstruction_fibre: BTreeSet::from([event]),
        };
        NativeTransportScaffold {
            schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
            address: "scaffold/native-loop".to_owned(),
            spools: vec![NativeSpool {
                schema: NATIVE_SPOOL_SCHEMA.to_owned(),
                address: "spool/native-loop".to_owned(),
                native_population: BTreeSet::from([native]),
                receiver_family: BTreeSet::from([receiver]),
                generator_family: BTreeSet::from([generator]),
                threads: vec![thread],
                serial_pullbacks: Vec::new(),
                generator_descents: vec![NativeGeneratorDescent {
                    generator,
                    steps: vec![NativeGeneratorStep {
                        from: native,
                        to: native,
                        thread: "thread/native-loop".to_owned(),
                    }],
                    open_domain: BTreeSet::new(),
                }],
                receiver_factors: vec![ReceiverFactor {
                    native,
                    receiver,
                    observation: Observation(5),
                }],
                mutual_constitutive_responses: Vec::new(),
                reconstruction_fibres: vec![NativeCollapsedFibre {
                    native,
                    occurrences: BTreeSet::from([event]),
                }],
                shortest_separators: Vec::new(),
                interchanges: Vec::new(),
                open_exterior: Vec::new(),
            }],
            compositions: Vec::new(),
            open_exterior: Vec::new(),
        }
    }

    fn witness(scaffold: &NativeTransportScaffold) -> ExteriorSoulkillerWitness {
        ExteriorSoulkillerWitness::seal(
            scaffold,
            ForeignRealizationTestimony {
                name: "inherited-transformer".to_owned(),
                format: "external-weight-container".to_owned(),
                artifact: ExteriorArtifactIdentity::measure(b"foreign realization"),
                topology: vec!["stack/block/0".to_owned()],
                coordinate_roles: vec!["foreign-operator-branch".to_owned()],
            },
            ForeignExecutionTestimony {
                runtime: "bounded-source-runtime".to_owned(),
                device: "resident-card".to_owned(),
                apparatus: ExteriorArtifactIdentity::measure(b"apparatus receipt"),
                admitted_receiver_family: BTreeSet::from([ReceiverId(2)]),
                session_closed: true,
            },
            vec![ForeignFragmentTestimony {
                address: "fragment/block-0/query".to_owned(),
                coordinates: BTreeMap::from([("row".to_owned(), "0".to_owned())]),
                interventions: BTreeSet::from(["withdraw/block-0/query".to_owned()]),
            }],
            vec![ThreadExtractionWitness {
                native_thread: "thread/native-loop".to_owned(),
                founding_fragments: BTreeSet::from(["fragment/block-0/query".to_owned()]),
                checked_generator_word: vec![InputId(3)],
                receiver_family: BTreeSet::from([ReceiverId(2)]),
            }],
            vec![SpoolCondensationWitness {
                native_spool: "spool/native-loop".to_owned(),
                native_threads: BTreeSet::from(["thread/native-loop".to_owned()]),
                founding_fragments: BTreeSet::from(["fragment/block-0/query".to_owned()]),
                collapsed_fragment_fibres: Vec::new(),
                shortest_separators: Vec::new(),
            }],
            BTreeSet::from(["fragment/block-0/query".to_owned()]),
            BTreeSet::new(),
            vec!["unexcited source sections remain exterior".to_owned()],
        )
        .expect("sealed witness")
    }

    #[test]
    fn witness_is_separate_and_binds_the_exact_native_scaffold() {
        let scaffold = scaffold();
        let witness = witness(&scaffold);
        let bytes = witness.canonical_bytes(&scaffold).expect("witness bytes");
        let remounted =
            ExteriorSoulkillerWitness::read(&bytes, &scaffold).expect("witness remount");
        assert_eq!(remounted, witness);
    }

    #[test]
    fn witness_refuses_an_unknown_native_thread() {
        let scaffold = scaffold();
        let mut witness = witness(&scaffold);
        witness.thread_extractions[0].native_thread = "thread/not-in-scaffold".to_owned();
        assert!(matches!(
            witness.validate(&scaffold),
            Err(ExteriorSoulkillerWitnessRefusal::ThreadExtraction)
        ));
    }

    #[test]
    fn witness_refuses_a_live_foreign_session() {
        let scaffold = scaffold();
        let mut witness = witness(&scaffold);
        witness.execution.session_closed = false;
        assert!(matches!(
            witness.validate(&scaffold),
            Err(ExteriorSoulkillerWitnessRefusal::Execution)
        ));
    }
}
