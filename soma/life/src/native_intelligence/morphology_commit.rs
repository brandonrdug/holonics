//! Parented local morphology commits and exact circulation snapshots.
//!
//! A commit consumes one package owner, applies one genuinely later source-neutral deposit, and
//! returns one successor package. The retained deposit wire is exterior replay testimony; it never
//! routes conduct or identifies the ecology.

use std::collections::BTreeSet;

use holonic_engine::{
    native_spool::{
        NativeThreadDeposit, NativeThreadDepositReceipt, SituatedNativeTransportPredecessor,
    },
    EventId,
};
use serde::{Deserialize, Serialize};

use super::scaffold_cultivation::derive_returned_scaffold_deposit;
use super::world_return::constitute_world_interaction;
use super::{
    MorphologyLineage, NativeCirculationBoundary, NativeCirculationConfiguration,
    NativeCirculationSession, NativeEcologyRest, NativeMorphologyArtifact,
    NativeOwnedInferenceAddress, NativeSessionError, NativeWorldFace, NativeHolonMorphology,
};

pub const NATIVE_MORPHOLOGY_COMMIT_SCHEMA: &str = "soma-life.native-morphology-commit.v1";
pub const NATIVE_CIRCULATION_SNAPSHOT_SCHEMA: &str = "soma-life.native-circulation-snapshot.v1";
pub const NATIVE_CULTIVATION_CANDIDATE_SCHEMA: &str =
    "soma-life.native-cultivation-candidate.v2";

/// One staged exterior return. It borrows no morphology and cannot be committed against another
/// generation or emission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivationCandidate {
    pub(super) schema: String,
    pub(super) boundary: NativeCirculationBoundary,
    pub(super) faces: Vec<NativeWorldFace>,
    pub(super) returned_occurrence: EventId,
}

impl NativeCultivationCandidate {
    pub fn boundary(&self) -> &NativeCirculationBoundary {
        &self.boundary
    }

    pub fn faces(&self) -> &[NativeWorldFace] {
        &self.faces
    }

    pub fn returned_occurrence(&self) -> EventId {
        self.returned_occurrence
    }
}

/// Exact parented testimony for one local morphology commit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMorphologyCommit {
    pub schema: String,
    pub predecessor_lineage: MorphologyLineage,
    pub successor_lineage: MorphologyLineage,
    pub source: NativeOwnedInferenceAddress,
    pub emission: holonic_engine::native_ecology::holonic_intelligence::NativeEmissionAddress,
    pub returned_occurrence: EventId,
    pub causal_cone: BTreeSet<holonic_engine::receiver_history_compression::NativeStateId>,
    pub deposit_wire: Vec<u8>,
    pub deposit_receipt: NativeThreadDepositReceipt,
    pub interchange_population: usize,
    pub reconstruction_fibre_population: usize,
}

impl NativeMorphologyCommit {
    pub fn validate(&self) -> Result<(), NativeSessionError> {
        let deposit = self.deposit()?;
        self.deposit_receipt
            .validate()
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
        if self.schema != NATIVE_MORPHOLOGY_COMMIT_SCHEMA
            || self.predecessor_lineage.generation.checked_add(1)
                != Some(self.successor_lineage.generation)
            || self.successor_lineage.returned_occurrences
                != BTreeSet::from([self.returned_occurrence])
            || !self
                .successor_lineage
                .parent_occurrences
                .contains(&self.source.occurrence)
            || self
                .successor_lineage
                .parent_occurrences
                .contains(&self.returned_occurrence)
            || self.emission.entering_occurrence != self.source.occurrence
            || deposit.spool_address != self.source.spool
            || deposit.thread.address != self.deposit_receipt.thread_address
            || deposit.thread.occurrences.len() != 1
            || deposit.thread.occurrences[0].occurrence != self.returned_occurrence
            || deposit.thread.native_support != self.causal_cone
            || deposit.interchanges.len() != self.interchange_population
            || deposit.exact_reconstruction_fibres.len() != self.reconstruction_fibre_population
        {
            return Err(NativeSessionError::Commit(
                "the commit does not reconstruct its parented local deposit".to_owned(),
            ));
        }
        Ok(())
    }

    fn deposit(&self) -> Result<NativeThreadDeposit, NativeSessionError> {
        let deposit: NativeThreadDeposit = serde_json::from_slice(&self.deposit_wire)
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
        deposit
            .validate()
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
        Ok(deposit)
    }
}

/// A complete remountable session chart: one package plus its ordered parented commit testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationSnapshot {
    pub schema: String,
    pub package_wire: Vec<u8>,
    pub configuration: NativeCirculationConfiguration,
    pub commits: Vec<NativeMorphologyCommit>,
}

impl NativeCirculationSnapshot {
    pub fn read(bytes: &[u8]) -> Result<Self, NativeSessionError> {
        let snapshot: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeSessionError::Snapshot(error.to_string()))?;
        snapshot.validate()?;
        Ok(snapshot)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeSessionError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeSessionError::Snapshot(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), NativeSessionError> {
        if self.schema != NATIVE_CIRCULATION_SNAPSHOT_SCHEMA {
            return Err(NativeSessionError::Snapshot(
                "unknown circulation snapshot schema".to_owned(),
            ));
        }
        self.configuration.validate()?;
        let package = NativeMorphologyArtifact::read(&self.package_wire)?;
        let mut previous = None;
        for commit in &self.commits {
            commit.validate()?;
            if previous
                .is_some_and(|generation| generation != commit.predecessor_lineage.generation)
            {
                return Err(NativeSessionError::Snapshot(
                    "the commit journal generations do not join".to_owned(),
                ));
            }
            previous = Some(commit.successor_lineage.generation);
        }
        if previous.is_some_and(|generation| generation != package.manifest.lineage.generation) {
            return Err(NativeSessionError::Snapshot(
                "the journal terminal generation does not equal the package".to_owned(),
            ));
        }
        Ok(())
    }
}

impl NativeCirculationSession {
    /// Consume this generation and return its single committed successor.
    pub fn commit(
        self,
        candidate: NativeCultivationCandidate,
    ) -> Result<(Self, NativeMorphologyCommit), NativeSessionError> {
        candidate.boundary.validate_for(&self)?;
        if candidate.schema != NATIVE_CULTIVATION_CANDIDATE_SCHEMA {
            return Err(NativeSessionError::Return);
        }
        let constituted = constitute_world_interaction(
            &candidate.boundary,
            &candidate.faces,
            candidate.returned_occurrence,
        )?
        .map_err(|_| NativeSessionError::Return)?;
        let returned = constituted.interaction;
        if returned.emitted != candidate.boundary.emission.address
            || returned.occurrence <= candidate.boundary.request.address.occurrence
        {
            return Err(NativeSessionError::Return);
        }

        let NativeCirculationSession {
            package,
            configuration,
            mut commits,
        } = self;
        let predecessor_lineage = package.manifest.lineage.clone();
        let evaluation = package.evaluation.clone();
        let apparatus = package.manifest.realization.apparatus.clone();
        let exports = package.manifest.realization.exports.clone();
        let departed = package
            .testimony
            .departed_inherited_withdrawals
            .clone();
        let hot = package.into_hot();
        let parent_occurrences = hot_occurrences(&hot);
        let source = candidate.boundary.request.address.native();
        let deposit = derive_returned_scaffold_deposit(hot.native(), &source, &returned)
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
        let deposit_wire = serde_json::to_vec(&deposit)
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
        let interchange_population = deposit.interchanges.len();
        let reconstruction_fibre_population = deposit.exact_reconstruction_fibres.len();
        let causal_cone = deposit.thread.native_support.clone();
        let (hot, deposit_receipt) = apply_deposit(hot, deposit)?;
        let successor_lineage = MorphologyLineage {
            generation: predecessor_lineage
                .generation
                .checked_add(1)
                .ok_or_else(|| NativeSessionError::Commit("generation overflow".to_owned()))?,
            parent_occurrences,
            returned_occurrences: BTreeSet::from([returned.occurrence]),
        };
        let package = NativeMorphologyArtifact::found_successor(
            hot,
            successor_lineage.clone(),
            evaluation,
            apparatus,
            exports,
            departed,
        )?;
        let commit = NativeMorphologyCommit {
            schema: NATIVE_MORPHOLOGY_COMMIT_SCHEMA.to_owned(),
            predecessor_lineage,
            successor_lineage,
            source: candidate.boundary.request.address,
            emission: candidate.boundary.emission.address,
            returned_occurrence: returned.occurrence,
            causal_cone,
            deposit_wire,
            deposit_receipt,
            interchange_population,
            reconstruction_fibre_population,
        };
        commit.validate()?;
        commits.push(commit.clone());
        Ok((
            Self {
                package,
                configuration,
                commits,
            },
            commit,
        ))
    }

    pub fn snapshot(&self) -> Result<NativeCirculationSnapshot, NativeSessionError> {
        let snapshot = NativeCirculationSnapshot {
            schema: NATIVE_CIRCULATION_SNAPSHOT_SCHEMA.to_owned(),
            package_wire: self.package.canonical_bytes()?,
            configuration: self.configuration.clone(),
            commits: self.commits.clone(),
        };
        snapshot.validate()?;
        Ok(snapshot)
    }

    pub fn remount(snapshot: NativeCirculationSnapshot) -> Result<Self, NativeSessionError> {
        snapshot.validate()?;
        let package = NativeMorphologyArtifact::read(&snapshot.package_wire)?;
        let session = Self {
            package,
            configuration: snapshot.configuration,
            commits: snapshot.commits,
        };
        if session
            .commits
            .last()
            .is_some_and(|commit| commit.successor_lineage.generation != session.generation())
        {
            return Err(NativeSessionError::Snapshot(
                "the remounted package is not the journal successor".to_owned(),
            ));
        }
        Ok(session)
    }

    /// Consume the latest successor, invert its exact deposit, and return the predecessor owner.
    pub fn withdraw_last_commit(
        self,
    ) -> Result<(Self, NativeMorphologyCommit), NativeSessionError> {
        let NativeCirculationSession {
            package,
            configuration,
            mut commits,
        } = self;
        let commit = commits.pop().ok_or_else(|| {
            NativeSessionError::Commit("the session has no committed successor".to_owned())
        })?;
        if package.manifest.lineage != commit.successor_lineage {
            return Err(NativeSessionError::Commit(
                "the latest commit does not own this package generation".to_owned(),
            ));
        }
        let evaluation = package.evaluation.clone();
        let apparatus = package.manifest.realization.apparatus.clone();
        let exports = package.manifest.realization.exports.clone();
        let departed = package
            .testimony
            .departed_inherited_withdrawals
            .clone();
        let hot = package.into_hot();
        let NativeHolonMorphology::Situated { ecology, .. } = hot else {
            return Err(NativeSessionError::Commit(
                "a committed successor is not situated morphology".to_owned(),
            ));
        };
        let (predecessor, recovered_deposit) = ecology
            .withdraw_deposit(commit.deposit_receipt.clone())
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
        if recovered_deposit != commit.deposit()? {
            return Err(NativeSessionError::Commit(
                "withdrawal did not recover the committed local delta".to_owned(),
            ));
        }
        let hot = predecessor_hot(predecessor)?;
        let package = NativeMorphologyArtifact::found_successor(
            hot,
            commit.predecessor_lineage.clone(),
            evaluation,
            apparatus,
            exports,
            departed,
        )?;
        Ok((
            Self {
                package,
                configuration,
                commits,
            },
            commit,
        ))
    }

    /// Apply one previously withdrawn exact commit to its declared predecessor.
    pub fn replay_commit(self, commit: NativeMorphologyCommit) -> Result<Self, NativeSessionError> {
        commit.validate()?;
        if self.package.manifest.lineage != commit.predecessor_lineage {
            return Err(NativeSessionError::Commit(
                "the replay predecessor lineage does not match".to_owned(),
            ));
        }
        let NativeCirculationSession {
            package,
            configuration,
            mut commits,
        } = self;
        let evaluation = package.evaluation.clone();
        let apparatus = package.manifest.realization.apparatus.clone();
        let exports = package.manifest.realization.exports.clone();
        let departed = package
            .testimony
            .departed_inherited_withdrawals
            .clone();
        let hot = package.into_hot();
        let (hot, receipt) = apply_deposit(hot, commit.deposit()?)?;
        if receipt != commit.deposit_receipt {
            return Err(NativeSessionError::Commit(
                "replay returned a different inverse placement receipt".to_owned(),
            ));
        }
        let package = NativeMorphologyArtifact::found_successor(
            hot,
            commit.successor_lineage.clone(),
            evaluation,
            apparatus,
            exports,
            departed,
        )?;
        commits.push(commit);
        Ok(Self {
            package,
            configuration,
            commits,
        })
    }
}

fn hot_occurrences(hot: &NativeHolonMorphology) -> BTreeSet<EventId> {
    hot.native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence)
        .collect()
}

fn apply_deposit(
    hot: NativeHolonMorphology,
    deposit: NativeThreadDeposit,
) -> Result<(NativeHolonMorphology, NativeThreadDepositReceipt), NativeSessionError> {
    let (situated, receipt) = match hot {
        NativeHolonMorphology::Native(rest) => rest
            .ecology
            .deposit_thread(deposit)
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?,
        NativeHolonMorphology::Situated { ecology, .. } => ecology
            .deposit_thread(deposit)
            .map_err(|error| NativeSessionError::Commit(error.to_string()))?,
    };
    Ok((NativeHolonMorphology::situated(situated)?, receipt))
}

fn predecessor_hot(
    predecessor: SituatedNativeTransportPredecessor,
) -> Result<NativeHolonMorphology, NativeSessionError> {
    match predecessor {
        SituatedNativeTransportPredecessor::Native(native) => Ok(NativeHolonMorphology::Native(
            NativeEcologyRest::found(native)
                .map_err(|error| NativeSessionError::Commit(error.to_string()))?,
        )),
        SituatedNativeTransportPredecessor::Situated(situated) => {
            NativeHolonMorphology::situated(situated).map_err(Into::into)
        }
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

    use crate::native_intelligence::{
        consume_dismantling_return, InferenceConfigurationAddress, NativeWorldFace,
        NativeWorldStage,
    };

    fn excitation(event: u64, entering: u16, returned: u16) -> ForeignBf16Excitation {
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: None,
            entering_boundary: BoundaryId(event * 2),
            emitting_boundary: BoundaryId(event * 2 + 1),
            source_occurrence: format!("cold/{event}"),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![entering],
            returned_codewords: vec![returned],
            interventions: BTreeSet::from([format!("intervention/{event}")]),
            receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
        }
    }

    fn session() -> NativeCirculationSession {
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![excitation(1, 0x3f80, 0x4000), excitation(2, 0x4040, 0x4080)],
        })
        .expect("dismantle");
        let (hot, _) = consume_dismantling_return(returned).expect("hot");
        let package = NativeMorphologyArtifact::found(
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
                apparatus: "resident-native-word".to_owned(),
                stochastic_current: None,
            })
            .expect("configuration"),
        )
        .expect("session")
    }

    fn request(session: &NativeCirculationSession, occurrence: EventId) -> NativeInferenceRequest {
        let native = session.package().hot().native();
        let (spool, thread) = native
            .spools
            .iter()
            .flat_map(|spool| spool.threads.iter().map(move |thread| (spool, thread)))
            .find(|(_, thread)| {
                thread
                    .occurrences
                    .iter()
                    .any(|candidate| candidate.occurrence == occurrence)
            })
            .expect("addressed occurrence");
        NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: spool.address.clone(),
                thread: thread.address.clone(),
                occurrence,
            },
            receiver: ReceiverId(7),
        }
    }

    fn candidate(
        session: &NativeCirculationSession,
        boundary: &NativeCirculationBoundary,
        occurrence: u64,
    ) -> NativeCultivationCandidate {
        let faces = boundary
            .issued_world_faces()
            .into_iter()
            .map(|issued| {
                NativeWorldFace::report(
                    issued.clone(),
                    true,
                    issued.support().clone(),
                    b"admitted".to_vec(),
                )
                .expect("world face")
            })
            .collect();
        match session
            .stage_world_return(boundary, faces, EventId(occurrence))
            .expect("world return")
        {
            NativeWorldStage::Candidate { candidate, .. } => candidate,
            NativeWorldStage::Obstructed(obstruction) => {
                panic!("unexpected obstruction {obstruction:?}")
            }
        }
    }

    #[test]
    fn two_successive_commits_snapshot_remount_withdraw_and_replay_exactly() {
        let session = session();
        let first_boundary = session
            .conduct(request(&session, EventId(1)))
            .expect("first cut");
        let first_candidate = candidate(&session, &first_boundary, 100);
        let (session, first_commit) = session.commit(first_candidate).expect("first commit");
        assert_eq!(session.generation(), 1);
        assert_eq!(first_commit.predecessor_lineage.generation, 0);
        assert_eq!(first_commit.successor_lineage.generation, 1);

        let generation_one = session.package().canonical_bytes().expect("generation one");
        let second_boundary = session
            .conduct(request(&session, EventId(100)))
            .expect("second cut");
        let second_candidate = candidate(&session, &second_boundary, 101);
        let (session, _) = session.commit(second_candidate).expect("second commit");
        assert_eq!(session.generation(), 2);
        assert_eq!(session.commits().len(), 2);

        let generation_two = session.package().canonical_bytes().expect("generation two");
        let snapshot = session.snapshot().expect("snapshot");
        let snapshot_wire = snapshot.canonical_bytes().expect("snapshot wire");
        let remounted = NativeCirculationSession::remount(
            NativeCirculationSnapshot::read(&snapshot_wire).expect("read snapshot"),
        )
        .expect("remount");
        assert_eq!(
            remounted
                .package()
                .canonical_bytes()
                .expect("remounted package"),
            generation_two
        );
        assert_eq!(
            remounted
                .conduct(request(&remounted, EventId(101)))
                .expect("later conduct")
                .generation,
            2
        );

        let (predecessor, second_commit) = remounted
            .withdraw_last_commit()
            .expect("withdraw second commit");
        assert_eq!(predecessor.generation(), 1);
        assert_eq!(
            predecessor
                .package()
                .canonical_bytes()
                .expect("withdrawn predecessor"),
            generation_one
        );
        let replayed = predecessor
            .replay_commit(second_commit)
            .expect("replay second commit");
        assert_eq!(
            replayed
                .package()
                .canonical_bytes()
                .expect("replayed package"),
            generation_two
        );
    }

    #[test]
    fn incomplete_world_face_family_and_replay_predecessor_refuse() {
        let session = session();
        let boundary = session.conduct(request(&session, EventId(1))).expect("cut");
        let mut incomplete = boundary
            .issued_world_faces()
            .into_iter()
            .map(|issued| {
                NativeWorldFace::report(
                    issued.clone(),
                    true,
                    issued.support().clone(),
                    Vec::new(),
                )
                .expect("face")
            })
            .collect::<Vec<_>>();
        incomplete.pop();
        assert!(matches!(
            session.stage_world_return(&boundary, incomplete, EventId(100)),
            Err(NativeSessionError::WorldFace)
        ));

        let candidate = candidate(&session, &boundary, 100);
        let (successor, commit) = session.commit(candidate).expect("commit");
        assert!(matches!(
            successor.replay_commit(commit),
            Err(NativeSessionError::Commit(_))
        ));
    }
}
