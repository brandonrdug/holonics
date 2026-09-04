//! The fixed M1 sameness family. Each field is a distinct type and carries its own witness.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_value::{ExactOrdering, ExactValue};
use holonic_engine::ported_operation::PortedTransport;
use holonic_engine::{
    category::BoundaryId, causal::EventId, evolution::EvolutionLawId, interaction::InteractionId,
    ported_operation::PortedOperationComplex,
};
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::causal_section::CausalSectionReading;
use crate::mathematical_source::ExactBox;

use super::{
    CarrierId, MathematicalParticleError, OpenParticleFiber, PresentationFiberOccurrence,
    TypedPassage, ValueReceiverReturn,
};

/// A witness says that one typed relation stands, is separated, or remains open. Evidence
/// occurrences are checked against the particle body; prose alone cannot establish a relation.
mod diagram;
mod history;
mod receipt;
mod receivers;

pub use diagram::{DoctrineEquivalenceRelation, MarkedDiagramRelation};
pub use history::{ReceiverHistoryRelation, ReceiverHistoryReturn};
pub use receipt::{ByteRelationReceipt, TypedSamenessReceipt};
pub use receivers::{
    ClassificationReceiverReturn, ClassificationRelation, ReceiverFaceRelation,
    SimilarityReceiverReturn, SimilarityRelation,
};

use diagram::{validate_diagram, validate_doctrine};
use history::validate_receiver_history;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum RelationWitness {
    Established {
        evidence_occurrences: BTreeSet<String>,
    },
    Separated {
        shortest_separator: String,
    },
    Open {
        obstruction: String,
        reconstruction_fibre: BTreeSet<String>,
    },
}

impl RelationWitness {
    pub fn established(evidence_occurrences: BTreeSet<String>) -> Self {
        Self::Established {
            evidence_occurrences,
        }
    }

    pub fn separated(shortest_separator: impl Into<String>) -> Self {
        Self::Separated {
            shortest_separator: shortest_separator.into(),
        }
    }

    pub fn open(obstruction: impl Into<String>, reconstruction_fibre: BTreeSet<String>) -> Self {
        Self::Open {
            obstruction: obstruction.into(),
            reconstruction_fibre,
        }
    }

    fn validate(
        &self,
        relation: &'static str,
        evidence: &BTreeSet<String>,
    ) -> Result<(), MathematicalParticleError> {
        let held = match self {
            Self::Established {
                evidence_occurrences,
            } if !evidence_occurrences.is_empty() => evidence_occurrences,
            Self::Separated { shortest_separator } if !shortest_separator.is_empty() => {
                return evidence
                    .contains(shortest_separator)
                    .then_some(())
                    .ok_or(MathematicalParticleError::MalformedRelation(relation));
            }
            Self::Open {
                obstruction,
                reconstruction_fibre,
            } if !obstruction.is_empty() && !reconstruction_fibre.is_empty() => {
                reconstruction_fibre
            }
            _ => return Err(MathematicalParticleError::MalformedRelation(relation)),
        };
        held.iter()
            .all(|occurrence| evidence.contains(occurrence))
            .then_some(())
            .ok_or(MathematicalParticleError::MalformedRelation(relation))
    }

    fn is_established(&self) -> bool {
        matches!(self, Self::Established { .. })
    }

    fn is_open(&self) -> bool {
        matches!(self, Self::Open { .. })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OccurrenceRelation {
    pub left: String,
    pub right: String,
    pub witness: RelationWitness,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CarrierEqualityRelation {
    pub left_carrier: CarrierId,
    pub right_carrier: CarrierId,
    pub left: ExactValue,
    pub right: ExactValue,
    pub ordering: ExactOrdering,
    pub witness: RelationWitness,
}

impl CarrierEqualityRelation {
    pub fn compare(
        left_carrier: CarrierId,
        right_carrier: CarrierId,
        left: ExactValue,
        right: ExactValue,
        witness: RelationWitness,
    ) -> Self {
        let ordering = if left_carrier == right_carrier {
            left.compare(&right)
        } else {
            ExactOrdering::Open
        };
        Self {
            left_carrier,
            right_carrier,
            left,
            right,
            ordering,
            witness,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PresentationRelation {
    pub chart_occurrence: String,
    pub left: ExactBox,
    pub right: ExactBox,
    pub witness: RelationWitness,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteRelation {
    pub codec_occurrence: String,
    pub left: Vec<u8>,
    pub right: Vec<u8>,
    pub witness: RelationWitness,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DigestRelation {
    pub digest_map: String,
    pub left: String,
    pub right: String,
    pub witness: RelationWitness,
}

impl DigestRelation {
    pub fn sha256(left: &[u8], right: &[u8], witness: RelationWitness) -> Self {
        let hex = |bytes: &[u8]| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect()
        };
        Self {
            digest_map: "sha256".to_owned(),
            left: hex(left),
            right: hex(right),
            witness,
        }
    }
}

/// One pair's complete typed comparison panel. Diagram, doctrine, and receiver/history witnesses
/// are intentionally separate even when one occurrence supplies testimony for all three.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedSamenessFamily {
    pub(super) occurrence_identity: OccurrenceRelation,
    pub(super) carrier_equalities: Vec<CarrierEqualityRelation>,
    pub(super) marked_diagram_isomorphism: MarkedDiagramRelation,
    pub(super) doctrine_equivalence: DoctrineEquivalenceRelation,
    pub(super) receiver_history_equivalence: ReceiverHistoryRelation,
    pub(super) receiver_faces: Vec<ReceiverFaceRelation>,
    pub(super) classification: ClassificationRelation,
    pub(super) characteristic_similarity: SimilarityRelation,
    pub(super) presentation: PresentationRelation,
    pub(super) bytes: ByteRelation,
    pub(super) digest: DigestRelation,
}

impl TypedSamenessFamily {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        occurrence_identity: OccurrenceRelation,
        carrier_equalities: Vec<CarrierEqualityRelation>,
        marked_diagram_isomorphism: MarkedDiagramRelation,
        doctrine_equivalence: DoctrineEquivalenceRelation,
        receiver_history_equivalence: ReceiverHistoryRelation,
        receiver_faces: Vec<ReceiverFaceRelation>,
        classification: ClassificationRelation,
        characteristic_similarity: SimilarityRelation,
        presentation: PresentationRelation,
        bytes: ByteRelation,
        digest: DigestRelation,
        particle_occurrence: &str,
        source_occurrences: &BTreeSet<String>,
        carriers: &BTreeSet<CarrierId>,
        operation: &PortedOperationComplex,
        passages: &[TypedPassage],
        presentation_fibres: &[PresentationFiberOccurrence],
        open_fibres: &[OpenParticleFiber],
        value_receivers: &[ValueReceiverReturn],
        classification_receivers: &[ClassificationReceiverReturn],
        similarity_receivers: &[SimilarityReceiverReturn],
        receiver_history_returns: &[ReceiverHistoryReturn],
    ) -> Result<Self, MathematicalParticleError> {
        let result = Self {
            occurrence_identity,
            carrier_equalities,
            marked_diagram_isomorphism,
            doctrine_equivalence,
            receiver_history_equivalence,
            receiver_faces,
            classification,
            characteristic_similarity,
            presentation,
            bytes,
            digest,
        };
        let evidence = sameness_evidence(
            particle_occurrence,
            source_occurrences,
            passages,
            presentation_fibres,
            open_fibres,
            value_receivers,
            classification_receivers,
            similarity_receivers,
            receiver_history_returns,
        );
        result.validate(
            &evidence,
            carriers,
            source_occurrences,
            operation,
            passages,
            presentation_fibres,
            open_fibres,
            value_receivers,
            classification_receivers,
            similarity_receivers,
            receiver_history_returns,
        )?;
        Ok(result)
    }

    pub(super) fn validate(
        &self,
        evidence: &BTreeSet<String>,
        carriers: &BTreeSet<CarrierId>,
        source_occurrences: &BTreeSet<String>,
        operation: &PortedOperationComplex,
        passages: &[TypedPassage],
        presentation_fibres: &[PresentationFiberOccurrence],
        open_fibres: &[OpenParticleFiber],
        value_receivers: &[ValueReceiverReturn],
        classification_receivers: &[ClassificationReceiverReturn],
        similarity_receivers: &[SimilarityReceiverReturn],
        receiver_history_returns: &[ReceiverHistoryReturn],
    ) -> Result<(), MathematicalParticleError> {
        if !evidence.contains(&self.occurrence_identity.left)
            || !evidence.contains(&self.occurrence_identity.right)
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "occurrence-identity",
            ));
        }
        self.occurrence_identity
            .witness
            .validate("occurrence-identity", evidence)?;
        if self.occurrence_identity.witness.is_established()
            != (self.occurrence_identity.left == self.occurrence_identity.right)
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "occurrence-identity",
            ));
        }
        if self.carrier_equalities.is_empty() || self.receiver_faces.is_empty() {
            return Err(MathematicalParticleError::MalformedRelation(
                "carrier-or-receiver-face",
            ));
        }
        for relation in &self.carrier_equalities {
            if !carriers.contains(&relation.left_carrier)
                || !carriers.contains(&relation.right_carrier)
            {
                return Err(MathematicalParticleError::MalformedRelation(
                    "carrier-equality",
                ));
            }
            validate_ordering(
                relation.ordering,
                &relation.witness,
                "carrier-equality",
                evidence,
            )?;
        }
        validate_diagram(
            &self.marked_diagram_isomorphism,
            evidence,
            source_occurrences,
            operation,
            passages,
            presentation_fibres,
            open_fibres,
        )?;
        let ports = operation
            .shape
            .boundaries
            .objects
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        validate_doctrine(&self.doctrine_equivalence, evidence, &ports)?;
        let history_return = receiver_history_returns
            .iter()
            .find(|returned| {
                returned.occurrence() == self.receiver_history_equivalence.return_occurrence
            })
            .ok_or(MathematicalParticleError::MalformedRelation(
                "receiver-history-equivalence",
            ))?;
        let expected_history = ReceiverHistoryRelation::from_return(
            &self.occurrence_identity.left,
            &self.occurrence_identity.right,
            history_return,
        )?;
        if expected_history != self.receiver_history_equivalence {
            return Err(MathematicalParticleError::MalformedRelation(
                "receiver-history-equivalence",
            ));
        }
        validate_receiver_history(
            &self.receiver_history_equivalence,
            &self.occurrence_identity.left,
            &self.occurrence_identity.right,
            evidence,
        )?;
        for relation in &self.receiver_faces {
            let returned = value_receivers
                .iter()
                .find(|returned| returned.occurrence() == relation.receiver_occurrence);
            if !evidence.contains(&relation.receiver_occurrence)
                || returned.is_none_or(|returned| {
                    returned.values().get(relation.left_index) != Some(&relation.left)
                        || returned.values().get(relation.right_index) != Some(&relation.right)
                })
            {
                return Err(MathematicalParticleError::MalformedRelation(
                    "receiver-face",
                ));
            }
            validate_ordering(
                relation.ordering,
                &relation.witness,
                "receiver-face",
                evidence,
            )?;
        }
        let classification_return = classification_receivers
            .iter()
            .find(|returned| returned.occurrence() == self.classification.classifier_occurrence)
            .ok_or(MathematicalParticleError::MalformedRelation(
                "classification",
            ))?;
        if classification_return
            .classes()
            .get(&self.classification.left_subject)
            != Some(&self.classification.left_class)
            || classification_return
                .classes()
                .get(&self.classification.right_subject)
                != Some(&self.classification.right_class)
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "classification",
            ));
        }
        validate_equality(
            self.classification.left_class == self.classification.right_class,
            &self.classification.witness,
            "classification",
            evidence,
        )?;
        if !evidence.contains(&self.classification.classifier_occurrence) {
            return Err(MathematicalParticleError::MalformedRelation(
                "classification",
            ));
        }
        let similarity_return = similarity_receivers
            .iter()
            .find(|returned| {
                returned.occurrence() == self.characteristic_similarity.receiver_occurrence
            })
            .ok_or(MathematicalParticleError::MalformedRelation(
                "characteristic-similarity",
            ))?;
        let expected_similarity = SimilarityRelation::from_return(
            similarity_return,
            &self.characteristic_similarity.left_subject,
            &self.characteristic_similarity.right_subject,
        )?;
        if expected_similarity != self.characteristic_similarity {
            return Err(MathematicalParticleError::MalformedRelation(
                "characteristic-similarity",
            ));
        }
        let similarity_equal = !self.characteristic_similarity.characteristics.is_empty()
            && self
                .characteristic_similarity
                .characteristics
                .values()
                .all(|(left, right)| left == right);
        if !evidence.contains(&self.characteristic_similarity.receiver_occurrence)
            || !evidence.contains(&self.presentation.chart_occurrence)
            || !evidence.contains(&self.bytes.codec_occurrence)
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "comparison-receiver-occurrence",
            ));
        }
        validate_equality(
            similarity_equal,
            &self.characteristic_similarity.witness,
            "characteristic-similarity",
            evidence,
        )?;
        validate_equality(
            self.presentation.left == self.presentation.right,
            &self.presentation.witness,
            "presentation-equality",
            evidence,
        )?;
        validate_equality(
            self.bytes.left == self.bytes.right,
            &self.bytes.witness,
            "byte-equality",
            evidence,
        )?;
        validate_equality(
            self.digest.left == self.digest.right,
            &self.digest.witness,
            "digest-equality",
            evidence,
        )?;
        Ok(())
    }
}

fn sameness_evidence(
    particle_occurrence: &str,
    source_occurrences: &BTreeSet<String>,
    passages: &[TypedPassage],
    presentation_fibres: &[PresentationFiberOccurrence],
    open_fibres: &[OpenParticleFiber],
    value_receivers: &[ValueReceiverReturn],
    classification_receivers: &[ClassificationReceiverReturn],
    similarity_receivers: &[SimilarityReceiverReturn],
    receiver_history_returns: &[ReceiverHistoryReturn],
) -> BTreeSet<String> {
    let mut evidence = source_occurrences.clone();
    evidence.insert(particle_occurrence.to_owned());
    evidence.extend(
        passages
            .iter()
            .map(|passage| passage.occurrence().to_owned()),
    );
    evidence.extend(
        passages
            .iter()
            .flat_map(|passage| passage.branches().values())
            .map(|word| word.occurrence.clone()),
    );
    evidence.extend(
        presentation_fibres
            .iter()
            .map(|fibre| fibre.occurrence.clone()),
    );
    evidence.extend(open_fibres.iter().map(|fibre| fibre.occurrence.clone()));
    evidence.extend(
        value_receivers
            .iter()
            .map(|returned| returned.occurrence().to_owned()),
    );
    evidence.extend(
        classification_receivers
            .iter()
            .map(|returned| returned.occurrence().to_owned()),
    );
    evidence.extend(
        similarity_receivers
            .iter()
            .map(|returned| returned.occurrence().to_owned()),
    );
    evidence.extend(
        receiver_history_returns
            .iter()
            .map(|returned| returned.occurrence().to_owned()),
    );
    evidence
}

fn validate_ordering(
    ordering: ExactOrdering,
    witness: &RelationWitness,
    relation: &'static str,
    evidence: &BTreeSet<String>,
) -> Result<(), MathematicalParticleError> {
    witness.validate(relation, evidence)?;
    match ordering {
        ExactOrdering::Equal if witness.is_established() => Ok(()),
        ExactOrdering::Open if witness.is_open() => Ok(()),
        ExactOrdering::Less | ExactOrdering::Greater
            if !witness.is_established() && !witness.is_open() =>
        {
            Ok(())
        }
        _ => Err(MathematicalParticleError::MalformedRelation(relation)),
    }
}

fn validate_equality(
    equal: bool,
    witness: &RelationWitness,
    relation: &'static str,
    evidence: &BTreeSet<String>,
) -> Result<(), MathematicalParticleError> {
    witness.validate(relation, evidence)?;
    if equal == witness.is_established() || (!equal && witness.is_open()) {
        Ok(())
    } else {
        Err(MathematicalParticleError::MalformedRelation(relation))
    }
}
