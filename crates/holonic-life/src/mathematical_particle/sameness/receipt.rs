use super::*;

/// Payload-free byte testimony. The codec occurrence and exact payload extents remain visible,
/// while the payload bodies are represented only by their collision-resistant identities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ByteRelationReceipt {
    codec_occurrence: String,
    left_octets: usize,
    right_octets: usize,
    left_sha256: String,
    right_sha256: String,
    witness: RelationWitness,
}

impl ByteRelationReceipt {
    pub fn codec_occurrence(&self) -> &str {
        &self.codec_occurrence
    }
    pub fn left_octets(&self) -> usize {
        self.left_octets
    }
    pub fn right_octets(&self) -> usize {
        self.right_octets
    }
    pub fn left_sha256(&self) -> &str {
        &self.left_sha256
    }
    pub fn right_sha256(&self) -> &str {
        &self.right_sha256
    }
    pub fn witness(&self) -> &RelationWitness {
        &self.witness
    }
}

/// Read-only serialized projection of one already-admitted sameness family.
///
/// There is deliberately no public constructor and no route from this projection back into an
/// admitted relation. Every field is copied from the family's validated, owner-private body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TypedSamenessReceipt {
    occurrence_identity: OccurrenceRelation,
    carrier_equalities: Vec<CarrierEqualityRelation>,
    marked_diagram_isomorphism: MarkedDiagramRelation,
    doctrine_equivalence: DoctrineEquivalenceRelation,
    receiver_history_equivalence: ReceiverHistoryRelation,
    receiver_faces: Vec<ReceiverFaceRelation>,
    classification: ClassificationRelation,
    characteristic_similarity: SimilarityRelation,
    presentation: PresentationRelation,
    bytes: ByteRelationReceipt,
    digest: DigestRelation,
}

impl TypedSamenessReceipt {
    pub fn occurrence_identity(&self) -> &OccurrenceRelation {
        &self.occurrence_identity
    }
    pub fn carrier_equalities(&self) -> &[CarrierEqualityRelation] {
        &self.carrier_equalities
    }
    pub fn marked_diagram_isomorphism(&self) -> &MarkedDiagramRelation {
        &self.marked_diagram_isomorphism
    }
    pub fn doctrine_equivalence(&self) -> &DoctrineEquivalenceRelation {
        &self.doctrine_equivalence
    }
    pub fn receiver_history_equivalence(&self) -> &ReceiverHistoryRelation {
        &self.receiver_history_equivalence
    }
    pub fn receiver_faces(&self) -> &[ReceiverFaceRelation] {
        &self.receiver_faces
    }
    pub fn classification(&self) -> &ClassificationRelation {
        &self.classification
    }
    pub fn characteristic_similarity(&self) -> &SimilarityRelation {
        &self.characteristic_similarity
    }
    pub fn presentation(&self) -> &PresentationRelation {
        &self.presentation
    }
    pub fn bytes(&self) -> &ByteRelationReceipt {
        &self.bytes
    }
    pub fn digest(&self) -> &DigestRelation {
        &self.digest
    }
}

impl TypedSamenessFamily {
    pub fn receipt(&self) -> TypedSamenessReceipt {
        let digest = |bytes: &[u8]| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect()
        };
        TypedSamenessReceipt {
            occurrence_identity: self.occurrence_identity.clone(),
            carrier_equalities: self.carrier_equalities.clone(),
            marked_diagram_isomorphism: self.marked_diagram_isomorphism.clone(),
            doctrine_equivalence: self.doctrine_equivalence.clone(),
            receiver_history_equivalence: self.receiver_history_equivalence.clone(),
            receiver_faces: self.receiver_faces.clone(),
            classification: self.classification.clone(),
            characteristic_similarity: self.characteristic_similarity.clone(),
            presentation: self.presentation.clone(),
            bytes: ByteRelationReceipt {
                codec_occurrence: self.bytes.codec_occurrence.clone(),
                left_octets: self.bytes.left.len(),
                right_octets: self.bytes.right.len(),
                left_sha256: digest(&self.bytes.left),
                right_sha256: digest(&self.bytes.right),
                witness: self.bytes.witness.clone(),
            },
            digest: self.digest.clone(),
        }
    }
}
